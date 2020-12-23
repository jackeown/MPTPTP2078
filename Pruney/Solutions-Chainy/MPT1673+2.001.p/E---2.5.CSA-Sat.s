%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:27 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  301 (29501757 expanded)
%              Number of clauses        :  291 (9297863 expanded)
%              Number of leaves         :    4 (10101939 expanded)
%              Depth                    :   40
%              Number of atoms          : 1571 (491114942 expanded)
%              Number of equality atoms :  317 (41980954 expanded)
%              Maximal formula depth    :   33 (   6 average)
%              Maximal clause size      :  107 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_waybel_0,conjecture,(
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
               => ( r1_yellow_0(X1,X2)
                <=> r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_waybel_0)).

fof(d7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r2_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X4,X5) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

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

fof(c_0_3,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
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

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( epred1_3(X3,X2,X1)
                 => ( r1_yellow_0(X1,X2)
                  <=> r1_yellow_0(X1,X3) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t53_waybel_0]),c_0_3])).

fof(c_0_5,plain,(
    ! [X6,X7,X9,X10,X12,X13,X16] :
      ( ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X7,esk1_2(X6,X7))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X7,X9)
        | r1_orders_2(X6,esk1_2(X6,X7),X9)
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X10),u1_struct_0(X6))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X7,esk2_3(X6,X7,X10))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,X10,esk2_3(X6,X7,X10))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_yellow_0])])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & epred1_3(esk8_0,esk7_0,esk6_0)
    & ( ~ r1_yellow_0(esk6_0,esk7_0)
      | ~ r1_yellow_0(esk6_0,esk8_0) )
    & ( r1_yellow_0(esk6_0,esk7_0)
      | r1_yellow_0(esk6_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( r1_yellow_0(esk6_0,esk7_0)
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

fof(c_0_10,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_lattice3(X17,X18,X19)
        | X19 != k1_yellow_0(X17,X18)
        | ~ r1_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X18,X20)
        | r1_orders_2(X17,X19,X20)
        | X19 != k1_yellow_0(X17,X18)
        | ~ r1_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_3(X17,X18,X19),u1_struct_0(X17))
        | ~ r2_lattice3(X17,X18,X19)
        | X19 = k1_yellow_0(X17,X18)
        | ~ r1_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( r2_lattice3(X17,X18,esk5_3(X17,X18,X19))
        | ~ r2_lattice3(X17,X18,X19)
        | X19 = k1_yellow_0(X17,X18)
        | ~ r1_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X19,esk5_3(X17,X18,X19))
        | ~ r2_lattice3(X17,X18,X19)
        | X19 = k1_yellow_0(X17,X18)
        | ~ r1_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_9])]),
    [final]).

cnf(c_0_14,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9])]),
    [final]).

cnf(c_0_17,plain,
    ( r2_lattice3(X1,X2,esk5_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_8]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_20,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_21,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_18]),c_0_9])])).

cnf(c_0_23,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_8]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_9])])).

cnf(c_0_26,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_23]),c_0_9])])).

cnf(c_0_27,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_8]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_8]),c_0_26]),c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_28]),c_0_9])]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_9])]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_11]),c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_32]),c_0_9])])).

cnf(c_0_36,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_11]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_11]),c_0_36]),c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_38]),c_0_9])])).

cnf(c_0_40,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_8]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_40]),c_0_9])])).

cnf(c_0_42,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_40]),c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_38]),c_0_9])])).

cnf(c_0_44,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_38]),c_0_9])])).

cnf(c_0_45,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_42]),c_0_9])])).

cnf(c_0_46,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_8]),c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_8]),c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_8]),c_0_46]),c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_48]),c_0_9])]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_50]),c_0_9])])).

cnf(c_0_52,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_40]),c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_40]),c_0_52]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_54]),c_0_9])])).

cnf(c_0_56,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_8]),c_0_46]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_56]),c_0_9])])).

cnf(c_0_58,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_56]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_56]),c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_56]),c_0_58]),c_0_59]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_61]),c_0_9])])).

cnf(c_0_63,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_11]),c_0_31])).

cnf(c_0_64,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_61]),c_0_9])])).

cnf(c_0_65,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_61]),c_0_9])])).

cnf(c_0_66,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_63]),c_0_9])])).

cnf(c_0_67,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_11]),c_0_31])).

cnf(c_0_68,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_11]),c_0_31])).

cnf(c_0_69,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_70,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_11]),c_0_67]),c_0_68])).

cnf(c_0_71,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_72,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_73,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_74,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_75,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_76,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
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
    inference(split_equiv,[status(thm)],[c_0_3])).

cnf(c_0_77,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_69]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_60]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_16]),c_0_9])]),
    [final]).

cnf(c_0_80,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r2_lattice3(X2,X3,esk3_3(X2,X3,X4))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_81,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_71]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_83,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | m1_subset_1(esk3_3(X2,X3,X4),u1_struct_0(X2))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_16]),c_0_9])]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_13]),c_0_9])]),
    [final]).

fof(c_0_88,plain,(
    ! [X25,X26,X27,X28,X29,X31] :
      ( ( ~ v1_finset_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | X28 = k1_xboole_0
        | r1_yellow_0(X25,X28)
        | ~ epred1_3(X27,X26,X25) )
      & ( v1_finset_1(esk9_4(X25,X26,X27,X29))
        | ~ r2_hidden(X29,X27)
        | ~ m1_subset_1(X29,u1_struct_0(X25))
        | ~ epred1_3(X27,X26,X25) )
      & ( m1_subset_1(esk9_4(X25,X26,X27,X29),k1_zfmisc_1(X26))
        | ~ r2_hidden(X29,X27)
        | ~ m1_subset_1(X29,u1_struct_0(X25))
        | ~ epred1_3(X27,X26,X25) )
      & ( r1_yellow_0(X25,esk9_4(X25,X26,X27,X29))
        | ~ r2_hidden(X29,X27)
        | ~ m1_subset_1(X29,u1_struct_0(X25))
        | ~ epred1_3(X27,X26,X25) )
      & ( X29 = k1_yellow_0(X25,esk9_4(X25,X26,X27,X29))
        | ~ r2_hidden(X29,X27)
        | ~ m1_subset_1(X29,u1_struct_0(X25))
        | ~ epred1_3(X27,X26,X25) )
      & ( ~ v1_finset_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(X26))
        | X31 = k1_xboole_0
        | r2_hidden(k1_yellow_0(X25,X31),X27)
        | ~ epred1_3(X27,X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])])])).

cnf(c_0_89,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_90,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,esk3_3(X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_91,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_92,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_60]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),X2)
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_79]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),X2)
    | m1_subset_1(esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_60]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_79]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_79]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_79]),
    [final]).

cnf(c_0_107,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = esk1_2(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_108,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = esk1_2(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_109,plain,
    ( X2 = esk1_2(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_110,plain,
    ( X1 = k1_yellow_0(X2,esk9_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_111,plain,
    ( m1_subset_1(esk9_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_112,plain,
    ( r1_yellow_0(X1,esk9_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_113,plain,
    ( v1_finset_1(esk9_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_8]),
    [final]).

cnf(c_0_116,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),X2)
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),X2)
    | m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),X2)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_94]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_124,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_94]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_13]),
    [final]).

cnf(c_0_126,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_94]),
    [final]).

cnf(c_0_127,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_79]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_84]),c_0_31]),c_0_102]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_100]),c_0_79]),
    [final]).

cnf(c_0_130,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),X2)
    | m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_131,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_104]),c_0_79]),
    [final]).

cnf(c_0_132,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_105]),c_0_79]),
    [final]).

cnf(c_0_133,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),X2)
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_134,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),X2)
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_135,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_106]),c_0_79]),
    [final]).

cnf(c_0_136,negated_conjecture,
    ( ~ r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_137,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_138,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,X1) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,X1,esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_139,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk5_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_140,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,X1) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_141,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_142,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,X1) = k1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_143,plain,
    ( k1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0))) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_110,c_0_78]),
    [final]).

cnf(c_0_144,negated_conjecture,
    ( epred1_3(esk8_0,esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_145,plain,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_111,c_0_78]),
    [final]).

cnf(c_0_146,plain,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0)))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_112,c_0_78]),
    [final]).

cnf(c_0_147,plain,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v1_finset_1(esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0)))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_78]),
    [final]).

cnf(c_0_148,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_8]),c_0_115]),
    [final]).

cnf(c_0_149,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_8]),c_0_16]),
    [final]).

cnf(c_0_150,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_79]),
    [final]).

cnf(c_0_151,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_105]),c_0_79]),
    [final]).

cnf(c_0_152,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_106]),c_0_79]),
    [final]).

cnf(c_0_153,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_79]),c_0_13]),c_0_79]),
    [final]).

cnf(c_0_154,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_79]),c_0_13]),c_0_79]),
    [final]).

cnf(c_0_155,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_79]),c_0_13]),c_0_79]),
    [final]).

cnf(c_0_156,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_79]),
    [final]).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_79]),
    [final]).

cnf(c_0_158,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),X2)
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_159,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = esk1_2(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk2_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_160,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = esk1_2(esk6_0,X1)
    | m1_subset_1(esk2_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_161,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = esk1_2(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk2_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_162,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(esk6_0,esk8_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_163,plain,
    ( k1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0))) = esk1_2(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_110,c_0_29]),
    [final]).

cnf(c_0_164,plain,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_111,c_0_29]),
    [final]).

cnf(c_0_165,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk1_2(esk6_0,esk8_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_166,plain,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0)))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_112,c_0_29]),
    [final]).

cnf(c_0_167,plain,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | v1_finset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0)))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_29]),
    [final]).

cnf(c_0_168,plain,
    ( k1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0))) = esk1_2(esk6_0,esk7_0)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_110,c_0_13]),
    [final]).

cnf(c_0_169,plain,
    ( m1_subset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0)),k1_zfmisc_1(X1))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_111,c_0_13]),
    [final]).

cnf(c_0_170,plain,
    ( v1_finset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_13]),
    [final]).

cnf(c_0_171,plain,
    ( m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0)))
    | ~ epred1_3(X2,X1,esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_112,c_0_13]),
    [final]).

cnf(c_0_172,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_173,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_174,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_175,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_176,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_121]),c_0_78]),c_0_79]),
    [final]).

cnf(c_0_177,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_122]),c_0_78]),c_0_79]),
    [final]).

cnf(c_0_178,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_100]),c_0_78]),c_0_94]),
    [final]).

cnf(c_0_179,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_124]),c_0_78]),c_0_79]),
    [final]).

cnf(c_0_180,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_105]),c_0_78]),c_0_94]),
    [final]).

cnf(c_0_181,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_104]),c_0_78]),c_0_94]),
    [final]).

cnf(c_0_182,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_94]),c_0_79]),
    [final]).

cnf(c_0_183,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_126]),c_0_78]),c_0_79]),
    [final]).

cnf(c_0_184,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_106]),c_0_78]),c_0_94]),
    [final]).

cnf(c_0_185,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_121]),c_0_79]),
    [final]).

cnf(c_0_186,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_121]),c_0_94]),
    [final]).

cnf(c_0_187,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_122]),c_0_79]),
    [final]).

cnf(c_0_188,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_122]),c_0_94]),
    [final]).

cnf(c_0_189,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_100]),c_0_94]),
    [final]).

cnf(c_0_190,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_124]),c_0_79]),
    [final]).

cnf(c_0_191,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_124]),c_0_94]),
    [final]).

cnf(c_0_192,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_105]),c_0_94]),
    [final]).

cnf(c_0_193,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_104]),c_0_94]),
    [final]).

cnf(c_0_194,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_78]),
    [final]).

cnf(c_0_195,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_60]),
    [final]).

cnf(c_0_196,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_94]),c_0_78]),c_0_79]),
    [final]).

cnf(c_0_197,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_60]),
    [final]).

cnf(c_0_198,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_84]),c_0_31]),
    [final]).

cnf(c_0_199,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_78]),
    [final]).

cnf(c_0_200,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_126]),c_0_79]),
    [final]).

cnf(c_0_201,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_78]),
    [final]).

cnf(c_0_202,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_84]),c_0_31]),c_0_102]),
    [final]).

cnf(c_0_203,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_79]),c_0_13]),c_0_94]),
    [final]).

cnf(c_0_204,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_126]),c_0_94]),
    [final]).

cnf(c_0_205,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_106]),c_0_94]),
    [final]).

cnf(c_0_206,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_94]),c_0_78]),c_0_79]),
    [final]).

cnf(c_0_207,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),esk1_2(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_84]),c_0_31]),
    [final]).

cnf(c_0_208,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_79]),c_0_13]),c_0_94]),
    [final]).

cnf(c_0_209,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_78]),
    [final]).

cnf(c_0_210,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_78]),
    [final]).

cnf(c_0_211,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_121]),
    [final]).

cnf(c_0_212,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_122]),
    [final]).

cnf(c_0_213,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_124]),
    [final]).

cnf(c_0_214,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_126]),
    [final]).

cnf(c_0_215,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_115]),
    [final]).

cnf(c_0_216,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_16]),
    [final]).

cnf(c_0_217,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_115]),
    [final]).

cnf(c_0_218,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_16]),
    [final]).

cnf(c_0_219,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_220,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_11]),
    [final]).

cnf(c_0_221,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_11]),
    [final]).

cnf(c_0_222,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_115]),
    [final]).

cnf(c_0_223,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_16]),
    [final]).

cnf(c_0_224,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_115]),
    [final]).

cnf(c_0_225,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_78]),c_0_9])]),
    [final]).

cnf(c_0_226,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_115]),
    [final]).

cnf(c_0_227,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_16]),
    [final]).

cnf(c_0_228,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_115]),
    [final]).

cnf(c_0_229,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_16]),
    [final]).

cnf(c_0_230,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_115]),
    [final]).

cnf(c_0_231,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_11]),
    [final]).

cnf(c_0_232,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_16]),
    [final]).

cnf(c_0_233,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_11]),
    [final]).

cnf(c_0_234,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_11]),
    [final]).

cnf(c_0_235,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_11]),
    [final]).

cnf(c_0_236,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_143,c_0_144]),
    [final]).

cnf(c_0_237,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_16]),
    [final]).

cnf(c_0_238,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_11]),
    [final]).

cnf(c_0_239,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),k1_zfmisc_1(esk7_0))
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_144]),
    [final]).

cnf(c_0_240,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_144]),
    [final]).

cnf(c_0_241,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v1_finset_1(esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))
    | ~ r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_147,c_0_144]),
    [final]).

cnf(c_0_242,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115]),
    [final]).

cnf(c_0_243,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_16]),
    [final]).

cnf(c_0_244,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_11]),
    [final]).

cnf(c_0_245,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_60]),
    [final]).

cnf(c_0_246,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_78]),
    [final]).

cnf(c_0_247,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_60]),
    [final]).

cnf(c_0_248,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_151,c_0_60]),
    [final]).

cnf(c_0_249,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_94]),c_0_61]),c_0_79]),
    [final]).

cnf(c_0_250,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_152,c_0_60]),
    [final]).

cnf(c_0_251,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_153,c_0_60]),
    [final]).

cnf(c_0_252,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_154,c_0_60]),
    [final]).

cnf(c_0_253,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_155,c_0_60]),
    [final]).

cnf(c_0_254,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_156,c_0_60]),
    [final]).

cnf(c_0_255,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk7_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_60]),
    [final]).

cnf(c_0_256,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),esk1_2(esk6_0,esk8_0))
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_29]),
    [final]).

cnf(c_0_257,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_258,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_259,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_260,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_261,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_262,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_29]),c_0_9])]),
    [final]).

cnf(c_0_263,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = esk1_2(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk7_0,esk2_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_8]),
    [final]).

cnf(c_0_264,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_8]),
    [final]).

cnf(c_0_265,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = esk1_2(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk2_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_8]),
    [final]).

cnf(c_0_266,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_8]),
    [final]).

cnf(c_0_267,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = esk1_2(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk2_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_161,c_0_8]),
    [final]).

cnf(c_0_268,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_16]),c_0_84]),
    [final]).

cnf(c_0_269,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_11]),c_0_31]),
    [final]).

cnf(c_0_270,negated_conjecture,
    ( esk1_2(esk6_0,esk8_0) = k1_yellow_0(esk6_0,esk7_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_8]),
    [final]).

cnf(c_0_271,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk8_0))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_162,c_0_8]),
    [final]).

cnf(c_0_272,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0))) = esk1_2(esk6_0,esk8_0)
    | esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_144]),
    [final]).

cnf(c_0_273,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | m1_subset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0)),k1_zfmisc_1(esk7_0))
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_144]),
    [final]).

cnf(c_0_274,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))
    | r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_16]),c_0_84]),
    [final]).

cnf(c_0_275,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))
    | m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_11]),c_0_31]),
    [final]).

cnf(c_0_276,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk8_0))
    | r1_yellow_0(esk6_0,esk8_0)
    | ~ r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_165,c_0_8]),
    [final]).

cnf(c_0_277,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | r1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_166,c_0_144]),
    [final]).

cnf(c_0_278,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = k1_yellow_0(esk6_0,esk7_0)
    | v1_finset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0)))
    | ~ r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_167,c_0_144]),
    [final]).

cnf(c_0_279,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_100]),
    [final]).

cnf(c_0_280,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = esk1_2(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk2_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_281,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_104]),
    [final]).

cnf(c_0_282,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_105]),
    [final]).

cnf(c_0_283,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = esk1_2(esk6_0,X1)
    | m1_subset_1(esk2_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_284,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_yellow_0(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_106]),
    [final]).

cnf(c_0_285,negated_conjecture,
    ( esk1_2(esk6_0,esk7_0) = esk1_2(esk6_0,X1)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk2_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_13]),c_0_9])]),
    [final]).

cnf(c_0_286,negated_conjecture,
    ( k1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0))) = esk1_2(esk6_0,esk7_0)
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_168,c_0_144]),
    [final]).

cnf(c_0_287,negated_conjecture,
    ( m1_subset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0)),k1_zfmisc_1(esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_169,c_0_144]),
    [final]).

cnf(c_0_288,negated_conjecture,
    ( v1_finset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0)))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_170,c_0_144]),
    [final]).

cnf(c_0_289,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0)))
    | ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_171,c_0_144]),
    [final]).

cnf(c_0_290,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))
    | m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | r1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_8]),c_0_16]),
    [final]).

cnf(c_0_291,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,esk7_0),X2)
    | ~ epred1_3(X2,u1_struct_0(esk6_0),X1)
    | ~ v1_finset_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_172,c_0_173]),
    [final]).

cnf(c_0_292,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,esk8_0),X2)
    | ~ epred1_3(X2,u1_struct_0(esk6_0),X1)
    | ~ v1_finset_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_172,c_0_174]),
    [final]).

cnf(c_0_293,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_yellow_0(X1,esk7_0)
    | ~ epred1_3(X2,u1_struct_0(esk6_0),X1)
    | ~ v1_finset_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_175,c_0_173]),
    [final]).

cnf(c_0_294,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_yellow_0(X1,esk8_0)
    | ~ epred1_3(X2,u1_struct_0(esk6_0),X1)
    | ~ v1_finset_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_175,c_0_174]),
    [final]).

cnf(c_0_295,plain,
    ( r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_296,plain,
    ( r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_297,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_298,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_299,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_300,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 13:58:05 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.21/0.50  # and selection function SelectNewComplexAHP.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.028 s
% 0.21/0.50  # Presaturation interreduction done
% 0.21/0.50  
% 0.21/0.50  # No proof found!
% 0.21/0.50  # SZS status CounterSatisfiable
% 0.21/0.50  # SZS output start Saturation
% 0.21/0.50  fof(t53_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))=>(r1_yellow_0(X1,X2)<=>r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_waybel_0)).
% 0.21/0.50  fof(d7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(r1_yellow_0(X1,X2)<=>?[X3]:(((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4))))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_lattice3(X1,X2,X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X5)=>r1_orders_2(X1,X4,X5))))=>X4=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_yellow_0)).
% 0.21/0.50  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.21/0.50  fof(c_0_3, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), introduced(definition)).
% 0.21/0.50  fof(c_0_4, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>(r1_yellow_0(X1,X2)<=>r1_yellow_0(X1,X3))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t53_waybel_0]), c_0_3])).
% 0.21/0.50  fof(c_0_5, plain, ![X6, X7, X9, X10, X12, X13, X16]:(((((m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))|~r1_yellow_0(X6,X7)|~l1_orders_2(X6))&(r2_lattice3(X6,X7,esk1_2(X6,X7))|~r1_yellow_0(X6,X7)|~l1_orders_2(X6)))&(~m1_subset_1(X9,u1_struct_0(X6))|(~r2_lattice3(X6,X7,X9)|r1_orders_2(X6,esk1_2(X6,X7),X9))|~r1_yellow_0(X6,X7)|~l1_orders_2(X6)))&((m1_subset_1(esk2_3(X6,X7,X10),u1_struct_0(X6))|~r2_lattice3(X6,X7,X10)|X10=esk1_2(X6,X7)|~m1_subset_1(X10,u1_struct_0(X6))|~r1_yellow_0(X6,X7)|~l1_orders_2(X6))&((r2_lattice3(X6,X7,esk2_3(X6,X7,X10))|~r2_lattice3(X6,X7,X10)|X10=esk1_2(X6,X7)|~m1_subset_1(X10,u1_struct_0(X6))|~r1_yellow_0(X6,X7)|~l1_orders_2(X6))&(~r1_orders_2(X6,X10,esk2_3(X6,X7,X10))|~r2_lattice3(X6,X7,X10)|X10=esk1_2(X6,X7)|~m1_subset_1(X10,u1_struct_0(X6))|~r1_yellow_0(X6,X7)|~l1_orders_2(X6)))))&(((m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))&(((r2_lattice3(X6,X12,esk4_3(X6,X12,X13))|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))&(~m1_subset_1(X16,u1_struct_0(X6))|(~r2_lattice3(X6,X12,X16)|r1_orders_2(X6,esk4_3(X6,X12,X13),X16))|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6)))&(esk4_3(X6,X12,X13)!=X13|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))))&(((m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))|(r2_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))&(((r2_lattice3(X6,X12,esk4_3(X6,X12,X13))|(r2_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))&(~m1_subset_1(X16,u1_struct_0(X6))|(~r2_lattice3(X6,X12,X16)|r1_orders_2(X6,esk4_3(X6,X12,X13),X16))|(r2_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6)))&(esk4_3(X6,X12,X13)!=X13|(r2_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))))&((m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))|(~r1_orders_2(X6,X13,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))&(((r2_lattice3(X6,X12,esk4_3(X6,X12,X13))|(~r1_orders_2(X6,X13,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))&(~m1_subset_1(X16,u1_struct_0(X6))|(~r2_lattice3(X6,X12,X16)|r1_orders_2(X6,esk4_3(X6,X12,X13),X16))|(~r1_orders_2(X6,X13,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6)))&(esk4_3(X6,X12,X13)!=X13|(~r1_orders_2(X6,X13,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r2_lattice3(X6,X12,X13)))|r1_yellow_0(X6,X12)|~l1_orders_2(X6))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_yellow_0])])])])])])).
% 0.21/0.50  fof(c_0_6, negated_conjecture, ((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&l1_orders_2(esk6_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0)))&(epred1_3(esk8_0,esk7_0,esk6_0)&((~r1_yellow_0(esk6_0,esk7_0)|~r1_yellow_0(esk6_0,esk8_0))&(r1_yellow_0(esk6_0,esk7_0)|r1_yellow_0(esk6_0,esk8_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.21/0.50  cnf(c_0_7, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_8, negated_conjecture, (r1_yellow_0(esk6_0,esk7_0)|r1_yellow_0(esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  cnf(c_0_9, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  fof(c_0_10, plain, ![X17, X18, X19, X20]:(((r2_lattice3(X17,X18,X19)|X19!=k1_yellow_0(X17,X18)|~r1_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_lattice3(X17,X18,X20)|r1_orders_2(X17,X19,X20))|X19!=k1_yellow_0(X17,X18)|~r1_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17)))&((m1_subset_1(esk5_3(X17,X18,X19),u1_struct_0(X17))|~r2_lattice3(X17,X18,X19)|X19=k1_yellow_0(X17,X18)|~r1_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((r2_lattice3(X17,X18,esk5_3(X17,X18,X19))|~r2_lattice3(X17,X18,X19)|X19=k1_yellow_0(X17,X18)|~r1_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~r1_orders_2(X17,X19,esk5_3(X17,X18,X19))|~r2_lattice3(X17,X18,X19)|X19=k1_yellow_0(X17,X18)|~r1_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.21/0.50  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_12, plain, (m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.21/0.50  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_11]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_14, plain, (r2_lattice3(X1,X2,esk1_2(X1,X2))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_15, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_16, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|r1_yellow_0(esk6_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_17, plain, (r2_lattice3(X1,X2,esk5_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.21/0.50  cnf(c_0_18, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_8]), c_0_16])).
% 0.21/0.50  cnf(c_0_19, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_20, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk5_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.21/0.50  cnf(c_0_21, plain, (r1_orders_2(X2,esk1_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~r1_yellow_0(X2,X3)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_22, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_18]), c_0_9])])).
% 0.21/0.50  cnf(c_0_23, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_8]), c_0_16])).
% 0.21/0.50  cnf(c_0_24, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_25, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_9])])).
% 0.21/0.50  cnf(c_0_26, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_23]), c_0_9])])).
% 0.21/0.50  cnf(c_0_27, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_8]), c_0_16])).
% 0.21/0.50  cnf(c_0_28, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_8]), c_0_26]), c_0_27])).
% 0.21/0.50  cnf(c_0_29, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_28]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_30, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,X1)|m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_31, negated_conjecture, (r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_11]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_32, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_11]), c_0_31])).
% 0.21/0.50  cnf(c_0_33, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,X1)|r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_34, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_35, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_32]), c_0_9])])).
% 0.21/0.50  cnf(c_0_36, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_11]), c_0_31])).
% 0.21/0.50  cnf(c_0_37, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_11]), c_0_31])).
% 0.21/0.50  cnf(c_0_38, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_11]), c_0_36]), c_0_37])).
% 0.21/0.50  cnf(c_0_39, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_38]), c_0_9])])).
% 0.21/0.50  cnf(c_0_40, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_8]), c_0_16])).
% 0.21/0.50  cnf(c_0_41, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_40]), c_0_9])])).
% 0.21/0.50  cnf(c_0_42, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_40]), c_0_41])).
% 0.21/0.50  cnf(c_0_43, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_38]), c_0_9])])).
% 0.21/0.50  cnf(c_0_44, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_38]), c_0_9])])).
% 0.21/0.50  cnf(c_0_45, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_42]), c_0_9])])).
% 0.21/0.50  cnf(c_0_46, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_8]), c_0_16])).
% 0.21/0.50  cnf(c_0_47, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_yellow_0(esk6_0,esk8_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_8]), c_0_16])).
% 0.21/0.50  cnf(c_0_48, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_8]), c_0_46]), c_0_47])).
% 0.21/0.50  cnf(c_0_49, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_30, c_0_48])).
% 0.21/0.50  cnf(c_0_50, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_48]), c_0_9])]), c_0_49])).
% 0.21/0.50  cnf(c_0_51, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_50]), c_0_9])])).
% 0.21/0.50  cnf(c_0_52, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_40]), c_0_41])).
% 0.21/0.50  cnf(c_0_53, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_40]), c_0_41])).
% 0.21/0.50  cnf(c_0_54, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_40]), c_0_52]), c_0_53])).
% 0.21/0.50  cnf(c_0_55, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_54]), c_0_9])])).
% 0.21/0.50  cnf(c_0_56, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_8]), c_0_46]), c_0_47])).
% 0.21/0.50  cnf(c_0_57, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_56]), c_0_9])])).
% 0.21/0.50  cnf(c_0_58, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_56]), c_0_57])).
% 0.21/0.50  cnf(c_0_59, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_56]), c_0_57])).
% 0.21/0.50  cnf(c_0_60, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_56]), c_0_58]), c_0_59]), ['final']).
% 0.21/0.50  cnf(c_0_61, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_13, c_0_60])).
% 0.21/0.50  cnf(c_0_62, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,X1)|m1_subset_1(esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_61]), c_0_9])])).
% 0.21/0.50  cnf(c_0_63, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_11]), c_0_31])).
% 0.21/0.50  cnf(c_0_64, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,X1)|r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_61]), c_0_9])])).
% 0.21/0.50  cnf(c_0_65, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,X1)|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_61]), c_0_9])])).
% 0.21/0.50  cnf(c_0_66, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_63]), c_0_9])])).
% 0.21/0.50  cnf(c_0_67, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_11]), c_0_31])).
% 0.21/0.50  cnf(c_0_68, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_11]), c_0_31])).
% 0.21/0.50  cnf(c_0_69, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_70, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_11]), c_0_67]), c_0_68])).
% 0.21/0.50  cnf(c_0_71, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_72, plain, (r2_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_lattice3(X1,X2,esk3_3(X1,X2,X3))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_73, plain, (r2_lattice3(X1,X2,esk4_3(X1,X2,X3))|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_74, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,esk3_3(X1,X2,X3))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_75, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  fof(c_0_76, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_3])).
% 0.21/0.50  cnf(c_0_77, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_69]), ['final']).
% 0.21/0.50  cnf(c_0_78, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_70, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_79, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_16]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_80, plain, (r1_orders_2(X2,esk4_3(X2,X3,X4),X1)|r2_lattice3(X2,X3,esk3_3(X2,X3,X4))|r1_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_81, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_71]), ['final']).
% 0.21/0.50  cnf(c_0_82, negated_conjecture, (r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_83, plain, (r1_orders_2(X2,esk4_3(X2,X3,X4),X1)|m1_subset_1(esk3_3(X2,X3,X4),u1_struct_0(X2))|r1_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_84, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_16]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_85, negated_conjecture, (r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_86, negated_conjecture, (r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  fof(c_0_88, plain, ![X25, X26, X27, X28, X29, X31]:(((~v1_finset_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(X26))|(X28=k1_xboole_0|r1_yellow_0(X25,X28))|~epred1_3(X27,X26,X25))&(((v1_finset_1(esk9_4(X25,X26,X27,X29))|~r2_hidden(X29,X27)|~m1_subset_1(X29,u1_struct_0(X25))|~epred1_3(X27,X26,X25))&(m1_subset_1(esk9_4(X25,X26,X27,X29),k1_zfmisc_1(X26))|~r2_hidden(X29,X27)|~m1_subset_1(X29,u1_struct_0(X25))|~epred1_3(X27,X26,X25)))&((r1_yellow_0(X25,esk9_4(X25,X26,X27,X29))|~r2_hidden(X29,X27)|~m1_subset_1(X29,u1_struct_0(X25))|~epred1_3(X27,X26,X25))&(X29=k1_yellow_0(X25,esk9_4(X25,X26,X27,X29))|~r2_hidden(X29,X27)|~m1_subset_1(X29,u1_struct_0(X25))|~epred1_3(X27,X26,X25)))))&(~v1_finset_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(X26))|(X31=k1_xboole_0|r2_hidden(k1_yellow_0(X25,X31),X27))|~epred1_3(X27,X26,X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])])])).
% 0.21/0.50  cnf(c_0_89, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_90, plain, (r1_orders_2(X2,esk4_3(X2,X3,X4),X1)|r1_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~r1_orders_2(X2,X4,esk3_3(X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_91, plain, (r2_lattice3(X1,X2,esk4_3(X1,X2,X3))|r1_yellow_0(X1,X2)|~r1_orders_2(X1,X3,esk3_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_92, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|~r1_orders_2(X1,X3,esk3_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_93, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_94, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_79, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_95, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_96, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_97, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),X2)|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_98, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_99, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_100, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_101, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),X2)|m1_subset_1(esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_102, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_84, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_103, negated_conjecture, (r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_104, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_85, c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_105, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_86, c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_106, negated_conjecture, (m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_87, c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_107, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=esk1_2(X1,X2)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_108, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=esk1_2(X1,X2)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_109, plain, (X2=esk1_2(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_110, plain, (X1=k1_yellow_0(X2,esk9_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.21/0.50  cnf(c_0_111, plain, (m1_subset_1(esk9_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.21/0.50  cnf(c_0_112, plain, (r1_yellow_0(X1,esk9_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.21/0.50  cnf(c_0_113, plain, (v1_finset_1(esk9_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.21/0.50  cnf(c_0_114, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_115, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_89, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_116, negated_conjecture, (r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),X2)|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_117, negated_conjecture, (r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),X2)|m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_118, negated_conjecture, (r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),X2)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_119, negated_conjecture, (r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_120, negated_conjecture, (m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_121, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_93, c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_122, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_95, c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_123, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_124, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_96, c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_125, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_97, c_0_13]), ['final']).
% 0.21/0.50  cnf(c_0_126, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_98, c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_127, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_128, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_84]), c_0_31]), c_0_102]), ['final']).
% 0.21/0.50  cnf(c_0_129, negated_conjecture, (r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_100]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_130, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),X2)|m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_131, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_104]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_132, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_105]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_133, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),X2)|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_134, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),X2)|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_135, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_106]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_136, negated_conjecture, (~r1_yellow_0(esk6_0,esk7_0)|~r1_yellow_0(esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  cnf(c_0_137, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_138, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,X1)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,X1,esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_139, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|m1_subset_1(esk5_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_140, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,X1)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_141, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_142, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,X1)=k1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_143, plain, (k1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0)))=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|~epred1_3(X2,X1,esk6_0)|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_110, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_144, negated_conjecture, (epred1_3(esk8_0,esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  cnf(c_0_145, plain, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_111, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_146, plain, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0)))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_112, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_147, plain, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|v1_finset_1(esk9_4(esk6_0,X1,X2,k1_yellow_0(esk6_0,esk7_0)))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_113, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_148, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_8]), c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_149, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)|~m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_8]), c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_150, negated_conjecture, (r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_151, negated_conjecture, (r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_105]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_152, negated_conjecture, (r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_106]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_153, negated_conjecture, (r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_79]), c_0_13]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_154, negated_conjecture, (r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_79]), c_0_13]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_155, negated_conjecture, (r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_79]), c_0_13]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_156, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_119, c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_157, negated_conjecture, (m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_120, c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_158, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),X2)|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_159, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=esk1_2(esk6_0,X1)|r2_lattice3(esk6_0,X1,esk2_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_160, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=esk1_2(esk6_0,X1)|m1_subset_1(esk2_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_161, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=esk1_2(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk2_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_162, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(esk6_0,esk8_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_163, plain, (k1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0)))=esk1_2(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_110, c_0_29]), ['final']).
% 0.21/0.50  cnf(c_0_164, plain, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_111, c_0_29]), ['final']).
% 0.21/0.50  cnf(c_0_165, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,X1),esk1_2(esk6_0,esk8_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_166, plain, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0)))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_112, c_0_29]), ['final']).
% 0.21/0.50  cnf(c_0_167, plain, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|v1_finset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk8_0)))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_113, c_0_29]), ['final']).
% 0.21/0.50  cnf(c_0_168, plain, (k1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0)))=esk1_2(esk6_0,esk7_0)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_110, c_0_13]), ['final']).
% 0.21/0.50  cnf(c_0_169, plain, (m1_subset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0)),k1_zfmisc_1(X1))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_111, c_0_13]), ['final']).
% 0.21/0.50  cnf(c_0_170, plain, (v1_finset_1(esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_113, c_0_13]), ['final']).
% 0.21/0.50  cnf(c_0_171, plain, (m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk9_4(esk6_0,X1,X2,esk1_2(esk6_0,esk7_0)))|~epred1_3(X2,X1,esk6_0)|~r2_hidden(esk1_2(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_112, c_0_13]), ['final']).
% 0.21/0.50  cnf(c_0_172, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.21/0.50  cnf(c_0_173, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  cnf(c_0_174, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  cnf(c_0_175, plain, (X1=k1_xboole_0|r1_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.21/0.50  cnf(c_0_176, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_121]), c_0_78]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_177, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_122]), c_0_78]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_178, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_100]), c_0_78]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_179, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_124]), c_0_78]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_180, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_105]), c_0_78]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_181, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_104]), c_0_78]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_182, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_94]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_183, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_126]), c_0_78]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_184, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_106]), c_0_78]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_185, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_121]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_186, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_121]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_187, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_122]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_188, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_122]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_189, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_100]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_190, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_124]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_191, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_124]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_192, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_105]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_193, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_104]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_194, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_127, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_195, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_128, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_196, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_94]), c_0_78]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_197, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_129, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_198, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_84]), c_0_31]), ['final']).
% 0.21/0.50  cnf(c_0_199, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_131, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_200, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_126]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_201, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_132, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_202, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_84]), c_0_31]), c_0_102]), ['final']).
% 0.21/0.50  cnf(c_0_203, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_79]), c_0_13]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_204, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_126]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_205, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_106]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_206, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_94]), c_0_78]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_207, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),esk1_2(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk8_0,esk1_2(esk6_0,esk8_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_84]), c_0_31]), ['final']).
% 0.21/0.50  cnf(c_0_208, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_79]), c_0_13]), c_0_94]), ['final']).
% 0.21/0.50  cnf(c_0_209, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_135, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_210, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_97, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_211, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_121]), ['final']).
% 0.21/0.50  cnf(c_0_212, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_122]), ['final']).
% 0.21/0.50  cnf(c_0_213, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_124]), ['final']).
% 0.21/0.50  cnf(c_0_214, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_126]), ['final']).
% 0.21/0.50  cnf(c_0_215, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_137, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_216, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_137, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_217, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_138, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_218, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_138, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_219, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_220, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_137, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_221, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk8_0,esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_138, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_222, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_139, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_223, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_139, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_224, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_140, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_225, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk4_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_78]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_226, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_141, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_227, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_141, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_228, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_142, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_229, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|m1_subset_1(esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_140, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_230, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_123, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_231, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_139, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_232, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_142, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_233, negated_conjecture, (k1_yellow_0(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk8_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_141, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_234, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_142, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_235, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk2_3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_140, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_236, negated_conjecture, (k1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_143, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_237, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_123, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_238, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_123, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_239, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)),k1_zfmisc_1(esk7_0))|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_145, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_240, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_146, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_241, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|v1_finset_1(esk9_4(esk6_0,esk7_0,esk8_0,k1_yellow_0(esk6_0,esk7_0)))|~r2_hidden(k1_yellow_0(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_147, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_242, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_114, c_0_115]), ['final']).
% 0.21/0.50  cnf(c_0_243, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_114, c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_244, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_114, c_0_11]), ['final']).
% 0.21/0.50  cnf(c_0_245, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_148, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_246, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_149, c_0_78]), ['final']).
% 0.21/0.50  cnf(c_0_247, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_150, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_248, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_151, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_249, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_94]), c_0_61]), c_0_79]), ['final']).
% 0.21/0.50  cnf(c_0_250, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_152, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_251, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_153, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_252, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_154, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_253, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),k1_yellow_0(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_155, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_254, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_156, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_255, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk8_0)|m1_subset_1(esk4_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk7_0)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk3_3(esk6_0,esk7_0,k1_yellow_0(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_157, c_0_60]), ['final']).
% 0.21/0.50  cnf(c_0_256, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),esk1_2(esk6_0,esk8_0))|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_158, c_0_29]), ['final']).
% 0.21/0.50  cnf(c_0_257, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_258, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_259, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,X1,esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_260, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,X1,esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_261, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_262, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,X1)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk3_3(esk6_0,X1,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_29]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_263, negated_conjecture, (esk1_2(esk6_0,esk7_0)=esk1_2(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk7_0,esk2_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))|r1_yellow_0(esk6_0,esk8_0)|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_159, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_264, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r2_lattice3(esk6_0,esk7_0,esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))|r1_yellow_0(esk6_0,esk8_0)|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_33, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_265, negated_conjecture, (esk1_2(esk6_0,esk7_0)=esk1_2(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk2_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_160, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_266, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_30, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_267, negated_conjecture, (esk1_2(esk6_0,esk7_0)=esk1_2(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_yellow_0(esk6_0,esk8_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk2_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_161, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_268, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_16]), c_0_84]), ['final']).
% 0.21/0.50  cnf(c_0_269, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_11]), c_0_31]), ['final']).
% 0.21/0.50  cnf(c_0_270, negated_conjecture, (esk1_2(esk6_0,esk8_0)=k1_yellow_0(esk6_0,esk7_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_yellow_0(esk6_0,esk8_0)|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk5_3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0)))|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_34, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_271, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk7_0),esk1_2(esk6_0,esk8_0))|r1_yellow_0(esk6_0,esk8_0)|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))|~m1_subset_1(k1_yellow_0(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_162, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_272, negated_conjecture, (k1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0)))=esk1_2(esk6_0,esk8_0)|esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|~r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_163, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_273, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|m1_subset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0)),k1_zfmisc_1(esk7_0))|~r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_164, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_274, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))|r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_16]), c_0_84]), ['final']).
% 0.21/0.50  cnf(c_0_275, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk8_0),esk1_2(esk6_0,esk8_0))|m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_11]), c_0_31]), ['final']).
% 0.21/0.50  cnf(c_0_276, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk8_0))|r1_yellow_0(esk6_0,esk8_0)|~r2_lattice3(esk6_0,esk7_0,esk1_2(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_165, c_0_8]), ['final']).
% 0.21/0.50  cnf(c_0_277, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|r1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0)))|~r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_166, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_278, negated_conjecture, (esk1_2(esk6_0,esk7_0)=k1_yellow_0(esk6_0,esk7_0)|v1_finset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk8_0)))|~r2_hidden(esk1_2(esk6_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_167, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_279, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_100]), ['final']).
% 0.21/0.50  cnf(c_0_280, negated_conjecture, (esk1_2(esk6_0,esk7_0)=esk1_2(esk6_0,X1)|r2_lattice3(esk6_0,X1,esk2_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_281, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_104]), ['final']).
% 0.21/0.50  cnf(c_0_282, negated_conjecture, (r2_lattice3(esk6_0,esk7_0,esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_105]), ['final']).
% 0.21/0.50  cnf(c_0_283, negated_conjecture, (esk1_2(esk6_0,esk7_0)=esk1_2(esk6_0,X1)|m1_subset_1(esk2_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_284, negated_conjecture, (m1_subset_1(esk4_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk3_3(esk6_0,esk7_0,esk1_2(esk6_0,esk7_0)),u1_struct_0(esk6_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_yellow_0(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_136, c_0_106]), ['final']).
% 0.21/0.50  cnf(c_0_285, negated_conjecture, (esk1_2(esk6_0,esk7_0)=esk1_2(esk6_0,X1)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk2_3(esk6_0,X1,esk1_2(esk6_0,esk7_0)))|~r2_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_13]), c_0_9])]), ['final']).
% 0.21/0.50  cnf(c_0_286, negated_conjecture, (k1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0)))=esk1_2(esk6_0,esk7_0)|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_168, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_287, negated_conjecture, (m1_subset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0)),k1_zfmisc_1(esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_169, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_288, negated_conjecture, (v1_finset_1(esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0)))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|~r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_170, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_289, negated_conjecture, (m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk9_4(esk6_0,esk7_0,esk8_0,esk1_2(esk6_0,esk7_0)))|~r2_hidden(esk1_2(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_171, c_0_144]), ['final']).
% 0.21/0.50  cnf(c_0_290, negated_conjecture, (r1_orders_2(esk6_0,esk1_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0))|m1_subset_1(esk1_2(esk6_0,esk8_0),u1_struct_0(esk6_0))|r1_yellow_0(esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_8]), c_0_16]), ['final']).
% 0.21/0.50  cnf(c_0_291, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(k1_yellow_0(X1,esk7_0),X2)|~epred1_3(X2,u1_struct_0(esk6_0),X1)|~v1_finset_1(esk7_0)), inference(spm,[status(thm)],[c_0_172, c_0_173]), ['final']).
% 0.21/0.50  cnf(c_0_292, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(k1_yellow_0(X1,esk8_0),X2)|~epred1_3(X2,u1_struct_0(esk6_0),X1)|~v1_finset_1(esk8_0)), inference(spm,[status(thm)],[c_0_172, c_0_174]), ['final']).
% 0.21/0.50  cnf(c_0_293, negated_conjecture, (esk7_0=k1_xboole_0|r1_yellow_0(X1,esk7_0)|~epred1_3(X2,u1_struct_0(esk6_0),X1)|~v1_finset_1(esk7_0)), inference(spm,[status(thm)],[c_0_175, c_0_173]), ['final']).
% 0.21/0.50  cnf(c_0_294, negated_conjecture, (esk8_0=k1_xboole_0|r1_yellow_0(X1,esk8_0)|~epred1_3(X2,u1_struct_0(esk6_0),X1)|~v1_finset_1(esk8_0)), inference(spm,[status(thm)],[c_0_175, c_0_174]), ['final']).
% 0.21/0.50  cnf(c_0_295, plain, (r2_lattice3(X1,X2,esk3_3(X1,X2,X3))|r1_yellow_0(X1,X2)|esk4_3(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_296, plain, (r1_yellow_0(X1,X2)|esk4_3(X1,X2,X3)!=X3|~r1_orders_2(X1,X3,esk3_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_297, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|esk4_3(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.50  cnf(c_0_298, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  cnf(c_0_299, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  cnf(c_0_300, negated_conjecture, (v3_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.50  # SZS output end Saturation
% 0.21/0.50  # Proof object total steps             : 301
% 0.21/0.50  # Proof object clause steps            : 291
% 0.21/0.50  # Proof object formula steps           : 10
% 0.21/0.50  # Proof object conjectures             : 251
% 0.21/0.50  # Proof object clause conjectures      : 248
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 38
% 0.21/0.50  # Proof object initial formulas used   : 3
% 0.21/0.50  # Proof object generating inferences   : 251
% 0.21/0.50  # Proof object simplifying inferences  : 252
% 0.21/0.50  # Parsed axioms                        : 3
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 38
% 0.21/0.50  # Removed in clause preprocessing      : 0
% 0.21/0.50  # Initial clauses in saturation        : 38
% 0.21/0.50  # Processed clauses                    : 903
% 0.21/0.50  # ...of these trivial                  : 0
% 0.21/0.50  # ...subsumed                          : 399
% 0.21/0.50  # ...remaining for further processing  : 504
% 0.21/0.50  # Other redundant clauses eliminated   : 2
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 217
% 0.21/0.50  # Backward-rewritten                   : 0
% 0.21/0.50  # Generated clauses                    : 1641
% 0.21/0.50  # ...of the previous two non-trivial   : 1608
% 0.21/0.50  # Contextual simplify-reflections      : 123
% 0.21/0.50  # Paramodulations                      : 1639
% 0.21/0.50  # Factorizations                       : 0
% 0.21/0.50  # Equation resolutions                 : 2
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 247
% 0.21/0.50  #    Positive orientable unit clauses  : 6
% 0.21/0.50  #    Positive unorientable unit clauses: 0
% 0.21/0.50  #    Negative unit clauses             : 1
% 0.21/0.50  #    Non-unit-clauses                  : 240
% 0.21/0.50  # Current number of unprocessed clauses: 0
% 0.21/0.50  # ...number of literals in the above   : 0
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 255
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 22036
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 899
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 739
% 0.21/0.50  # Unit Clause-clause subsumption calls : 1
% 0.21/0.50  # Rewrite failures with RHS unbound    : 0
% 0.21/0.50  # BW rewrite match attempts            : 0
% 0.21/0.50  # BW rewrite match successes           : 0
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 72104
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.135 s
% 0.21/0.50  # System time              : 0.007 s
% 0.21/0.50  # Total time               : 0.142 s
% 0.21/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
