%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:29 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 197 expanded)
%              Number of clauses        :   32 (  57 expanded)
%              Number of leaves         :    3 (  66 expanded)
%              Depth                    :    6
%              Number of atoms          :  235 (2242 expanded)
%              Number of equality atoms :   21 ( 239 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_waybel_0,conjecture,(
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
                       => r2_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r2_yellow_0(X1,X5)
                                  & X4 = k2_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) )
               => ( r2_yellow_0(X1,X2)
                <=> r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_waybel_0)).

fof(t48_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

fof(c_0_2,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
    <=> ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) ) ) ),
    introduced(definition)).

fof(c_0_3,negated_conjecture,(
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
                 => ( r2_yellow_0(X1,X2)
                  <=> r2_yellow_0(X1,X3) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t58_waybel_0]),c_0_2])).

fof(c_0_4,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
     => ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_2])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X6))
        | ~ r2_yellow_0(X6,X7)
        | r2_yellow_0(X6,X8)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_lattice3(X6,X7,esk1_3(X6,X7,X8))
        | ~ r1_lattice3(X6,X8,esk1_3(X6,X7,X8))
        | ~ r2_yellow_0(X6,X7)
        | r2_yellow_0(X6,X8)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X7,esk1_3(X6,X7,X8))
        | r1_lattice3(X6,X8,esk1_3(X6,X7,X8))
        | ~ r2_yellow_0(X6,X7)
        | r2_yellow_0(X6,X8)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & epred1_3(esk4_0,esk3_0,esk2_0)
    & ( ~ r2_yellow_0(esk2_0,esk3_0)
      | ~ r2_yellow_0(esk2_0,esk4_0) )
    & ( r2_yellow_0(esk2_0,esk3_0)
      | r2_yellow_0(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16,X17,X19] :
      ( ( ~ v1_finset_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | X16 = k1_xboole_0
        | r2_yellow_0(X13,X16)
        | ~ epred1_3(X15,X14,X13) )
      & ( v1_finset_1(esk5_4(X13,X14,X15,X17))
        | ~ r2_hidden(X17,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ epred1_3(X15,X14,X13) )
      & ( m1_subset_1(esk5_4(X13,X14,X15,X17),k1_zfmisc_1(X14))
        | ~ r2_hidden(X17,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ epred1_3(X15,X14,X13) )
      & ( r2_yellow_0(X13,esk5_4(X13,X14,X15,X17))
        | ~ r2_hidden(X17,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ epred1_3(X15,X14,X13) )
      & ( X17 = k2_yellow_0(X13,esk5_4(X13,X14,X15,X17))
        | ~ r2_hidden(X17,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ epred1_3(X15,X14,X13) )
      & ( ~ v1_finset_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(X14))
        | X19 = k1_xboole_0
        | r2_hidden(k2_yellow_0(X13,X19),X15)
        | ~ epred1_3(X15,X14,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk3_0)
    | r2_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_12,plain,
    ( X1 = k2_yellow_0(X2,esk5_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])]),c_0_11]),
    [final]).

cnf(c_0_14,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_15,plain,
    ( r2_yellow_0(X1,esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_16,plain,
    ( v1_finset_1(esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_17,plain,
    ( k2_yellow_0(esk2_0,esk5_4(esk2_0,X1,X2,esk1_3(esk2_0,esk3_0,X3))) = esk1_3(esk2_0,esk3_0,X3)
    | r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X3)
    | ~ epred1_3(X2,X1,esk2_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( epred1_3(esk4_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_19,plain,
    ( r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X1)
    | m1_subset_1(esk5_4(esk2_0,X2,X3,esk1_3(esk2_0,esk3_0,X1)),k1_zfmisc_1(X2))
    | ~ epred1_3(X3,X2,esk2_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X1),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13]),
    [final]).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_22,plain,
    ( r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_23,plain,
    ( r2_yellow_0(esk2_0,esk5_4(esk2_0,X1,X2,esk1_3(esk2_0,esk3_0,X3)))
    | r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X3)
    | ~ epred1_3(X2,X1,esk2_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13]),
    [final]).

cnf(c_0_24,plain,
    ( v1_finset_1(esk5_4(esk2_0,X1,X2,esk1_3(esk2_0,esk3_0,X3)))
    | r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X3)
    | ~ epred1_3(X2,X1,esk2_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1))) = esk1_3(esk2_0,esk3_0,X1)
    | r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X1)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X1)
    | m1_subset_1(esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1)),k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk3_0),X2)
    | ~ epred1_3(X2,u1_struct_0(esk2_0),X1)
    | ~ v1_finset_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X1)
    | r1_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | r1_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_9]),c_0_10])]),c_0_11]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1)))
    | r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X1)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( v1_finset_1(esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1)))
    | r2_yellow_0(esk2_0,esk4_0)
    | r2_yellow_0(esk2_0,X1)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_0),X2)
    | ~ epred1_3(X2,u1_struct_0(esk2_0),X1)
    | ~ v1_finset_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_yellow_0(X1,esk3_0)
    | ~ epred1_3(X2,u1_struct_0(esk2_0),X1)
    | ~ v1_finset_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_yellow_0(X1,esk4_0)
    | ~ epred1_3(X2,u1_struct_0(esk2_0),X1)
    | ~ v1_finset_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25]),
    [final]).

cnf(c_0_36,plain,
    ( r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_yellow_0(esk2_0,esk3_0)
    | ~ r2_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.13/0.37  # and selection function SelectNewComplexAHP.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t58_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))=>(r2_yellow_0(X1,X2)<=>r2_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_waybel_0)).
% 0.13/0.37  fof(t48_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4)))&r2_yellow_0(X1,X2))=>r2_yellow_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_yellow_0)).
% 0.13/0.37  fof(c_0_2, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), introduced(definition)).
% 0.13/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>(r2_yellow_0(X1,X2)<=>r2_yellow_0(X1,X3))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t58_waybel_0]), c_0_2])).
% 0.13/0.37  fof(c_0_4, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_2])).
% 0.13/0.37  fof(c_0_5, plain, ![X6, X7, X8]:((m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X6))|~r2_yellow_0(X6,X7)|r2_yellow_0(X6,X8)|(v2_struct_0(X6)|~l1_orders_2(X6)))&((~r1_lattice3(X6,X7,esk1_3(X6,X7,X8))|~r1_lattice3(X6,X8,esk1_3(X6,X7,X8))|~r2_yellow_0(X6,X7)|r2_yellow_0(X6,X8)|(v2_struct_0(X6)|~l1_orders_2(X6)))&(r1_lattice3(X6,X7,esk1_3(X6,X7,X8))|r1_lattice3(X6,X8,esk1_3(X6,X7,X8))|~r2_yellow_0(X6,X7)|r2_yellow_0(X6,X8)|(v2_struct_0(X6)|~l1_orders_2(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(epred1_3(esk4_0,esk3_0,esk2_0)&((~r2_yellow_0(esk2_0,esk3_0)|~r2_yellow_0(esk2_0,esk4_0))&(r2_yellow_0(esk2_0,esk3_0)|r2_yellow_0(esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X13, X14, X15, X16, X17, X19]:(((~v1_finset_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(X14))|(X16=k1_xboole_0|r2_yellow_0(X13,X16))|~epred1_3(X15,X14,X13))&(((v1_finset_1(esk5_4(X13,X14,X15,X17))|~r2_hidden(X17,X15)|~m1_subset_1(X17,u1_struct_0(X13))|~epred1_3(X15,X14,X13))&(m1_subset_1(esk5_4(X13,X14,X15,X17),k1_zfmisc_1(X14))|~r2_hidden(X17,X15)|~m1_subset_1(X17,u1_struct_0(X13))|~epred1_3(X15,X14,X13)))&((r2_yellow_0(X13,esk5_4(X13,X14,X15,X17))|~r2_hidden(X17,X15)|~m1_subset_1(X17,u1_struct_0(X13))|~epred1_3(X15,X14,X13))&(X17=k2_yellow_0(X13,esk5_4(X13,X14,X15,X17))|~r2_hidden(X17,X15)|~m1_subset_1(X17,u1_struct_0(X13))|~epred1_3(X15,X14,X13)))))&(~v1_finset_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(X14))|(X19=k1_xboole_0|r2_hidden(k2_yellow_0(X13,X19),X15))|~epred1_3(X15,X14,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).
% 0.13/0.37  cnf(c_0_8, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (r2_yellow_0(esk2_0,esk3_0)|r2_yellow_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_12, plain, (X1=k2_yellow_0(X2,esk5_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X1)|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])]), c_0_11]), ['final']).
% 0.13/0.37  cnf(c_0_14, plain, (m1_subset_1(esk5_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_15, plain, (r2_yellow_0(X1,esk5_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_16, plain, (v1_finset_1(esk5_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_17, plain, (k2_yellow_0(esk2_0,esk5_4(esk2_0,X1,X2,esk1_3(esk2_0,esk3_0,X3)))=esk1_3(esk2_0,esk3_0,X3)|r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X3)|~epred1_3(X2,X1,esk2_0)|~r2_hidden(esk1_3(esk2_0,esk3_0,X3),X2)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (epred1_3(esk4_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_19, plain, (r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X1)|m1_subset_1(esk5_4(esk2_0,X2,X3,esk1_3(esk2_0,esk3_0,X1)),k1_zfmisc_1(X2))|~epred1_3(X3,X2,esk2_0)|~r2_hidden(esk1_3(esk2_0,esk3_0,X1),X3)), inference(spm,[status(thm)],[c_0_14, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_20, plain, (X1=k1_xboole_0|r2_hidden(k2_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_22, plain, (r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|r1_lattice3(X1,X3,esk1_3(X1,X2,X3))|r2_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.37  cnf(c_0_23, plain, (r2_yellow_0(esk2_0,esk5_4(esk2_0,X1,X2,esk1_3(esk2_0,esk3_0,X3)))|r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X3)|~epred1_3(X2,X1,esk2_0)|~r2_hidden(esk1_3(esk2_0,esk3_0,X3),X2)), inference(spm,[status(thm)],[c_0_15, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_24, plain, (v1_finset_1(esk5_4(esk2_0,X1,X2,esk1_3(esk2_0,esk3_0,X3)))|r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X3)|~epred1_3(X2,X1,esk2_0)|~r2_hidden(esk1_3(esk2_0,esk3_0,X3),X2)), inference(spm,[status(thm)],[c_0_16, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k2_yellow_0(esk2_0,esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1)))=esk1_3(esk2_0,esk3_0,X1)|r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X1)|~r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X1)|m1_subset_1(esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1)),k1_zfmisc_1(esk3_0))|~r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k2_yellow_0(X1,esk3_0),X2)|~epred1_3(X2,u1_struct_0(esk2_0),X1)|~v1_finset_1(esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X1)|r1_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))|r1_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_9]), c_0_10])]), c_0_11]), ['final']).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (r2_yellow_0(esk2_0,esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1)))|r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X1)|~r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (v1_finset_1(esk5_4(esk2_0,esk3_0,esk4_0,esk1_3(esk2_0,esk3_0,X1)))|r2_yellow_0(esk2_0,esk4_0)|r2_yellow_0(esk2_0,X1)|~r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k2_yellow_0(X1,esk4_0),X2)|~epred1_3(X2,u1_struct_0(esk2_0),X1)|~v1_finset_1(esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_25]), ['final']).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (esk3_0=k1_xboole_0|r2_yellow_0(X1,esk3_0)|~epred1_3(X2,u1_struct_0(esk2_0),X1)|~v1_finset_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_21]), ['final']).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (esk4_0=k1_xboole_0|r2_yellow_0(X1,esk4_0)|~epred1_3(X2,u1_struct_0(esk2_0),X1)|~v1_finset_1(esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_25]), ['final']).
% 0.13/0.37  cnf(c_0_36, plain, (r2_yellow_0(X1,X3)|v2_struct_0(X1)|~r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|~r1_lattice3(X1,X3,esk1_3(X1,X2,X3))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (~r2_yellow_0(esk2_0,esk3_0)|~r2_yellow_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 40
% 0.13/0.37  # Proof object clause steps            : 32
% 0.13/0.37  # Proof object formula steps           : 8
% 0.13/0.37  # Proof object conjectures             : 22
% 0.13/0.37  # Proof object clause conjectures      : 19
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 18
% 0.13/0.37  # Proof object initial formulas used   : 2
% 0.13/0.37  # Proof object generating inferences   : 14
% 0.13/0.37  # Proof object simplifying inferences  : 6
% 0.13/0.37  # Parsed axioms                        : 2
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 18
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 18
% 0.13/0.37  # Processed clauses                    : 52
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 2
% 0.13/0.37  # ...remaining for further processing  : 50
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 18
% 0.13/0.37  # ...of the previous two non-trivial   : 16
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 16
% 0.13/0.37  # Factorizations                       : 2
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 32
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 25
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 18
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 66
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 11
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2261
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
