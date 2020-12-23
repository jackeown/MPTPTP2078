%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:17 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   88 (1825 expanded)
%              Number of clauses        :   75 ( 630 expanded)
%              Number of leaves         :    6 ( 436 expanded)
%              Depth                    :   10
%              Number of atoms          :  375 (14793 expanded)
%              Number of equality atoms :   36 (1426 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   58 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_yellow_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k13_lattice3(X1,X2,X3)
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_0)).

fof(t38_orders_2,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ~ ( ? [X4] :
                        ( v6_orders_2(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X2,X4)
                        & r2_hidden(X3,X4) )
                    & ~ r1_orders_2(X1,X2,X3)
                    & ~ r1_orders_2(X1,X3,X2) )
                & ~ ( ( r1_orders_2(X1,X2,X3)
                      | r1_orders_2(X1,X3,X2) )
                    & ! [X4] :
                        ( ( v6_orders_2(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( r2_hidden(X2,X4)
                            & r2_hidden(X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( X2 = k13_lattice3(X1,X2,X3)
                <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_0])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v6_orders_2(X15,X12)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X14,X15)
        | r1_orders_2(X12,X13,X14)
        | r1_orders_2(X12,X14,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( v6_orders_2(esk1_3(X12,X13,X14),X12)
        | ~ r1_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r1_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(X13,esk1_3(X12,X13,X14))
        | ~ r1_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(X14,esk1_3(X12,X13,X14))
        | ~ r1_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( v6_orders_2(esk1_3(X12,X13,X14),X12)
        | ~ r1_orders_2(X12,X14,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r1_orders_2(X12,X14,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(X13,esk1_3(X12,X13,X14))
        | ~ r1_orders_2(X12,X14,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(X14,esk1_3(X12,X13,X14))
        | ~ r1_orders_2(X12,X14,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v3_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & v1_lattice3(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( esk3_0 != k13_lattice3(esk2_0,esk3_0,esk4_0)
      | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) )
    & ( esk3_0 = k13_lattice3(esk2_0,esk3_0,esk4_0)
      | r1_orders_2(esk2_0,esk4_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( v2_struct_0(X10)
      | ~ v3_orders_2(X10)
      | ~ l1_orders_2(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | r1_orders_2(X10,X11,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_14,plain,(
    ! [X8] :
      ( ~ v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 = k13_lattice3(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_20,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

fof(c_0_22,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_16])]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_28,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_13])]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_13])]),
    [final]).

cnf(c_0_34,plain,
    ( v6_orders_2(esk1_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_35,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_36,plain,
    ( v6_orders_2(esk1_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_37,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_38,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_39,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,esk3_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_11])]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_43,plain,
    ( r1_orders_2(X2,X3,X4)
    | r1_orders_2(X2,X4,X3)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,X1)
    | ~ v6_orders_2(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk3_0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_19]),c_0_16])]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_16])]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_19]),c_0_11])]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_19]),c_0_16])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_19]),c_0_11])]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,X1)
    | ~ v6_orders_2(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_19]),c_0_11])]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk3_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_16])]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_51]),c_0_16])]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_16])]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk4_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_53]),c_0_11])]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_53]),c_0_11])]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_11])]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_25]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_58]),c_0_59]),c_0_60]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_41]),c_0_25]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_62]),c_0_60]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_63]),c_0_64]),c_0_65]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_66]),c_0_67]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_63]),c_0_65]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_66]),c_0_68]),c_0_67]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_60]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_65]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_67]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 != k13_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.14/0.38  # and selection function SelectNewComplexAHP.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t24_yellow_0, conjecture, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_0)).
% 0.14/0.38  fof(t38_orders_2, axiom, ![X1]:((v3_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(~(((?[X4]:(((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))&r2_hidden(X2,X4))&r2_hidden(X3,X4))&~(r1_orders_2(X1,X2,X3)))&~(r1_orders_2(X1,X3,X2))))&~(((r1_orders_2(X1,X2,X3)|r1_orders_2(X1,X3,X2))&![X4]:((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~((r2_hidden(X2,X4)&r2_hidden(X3,X4)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_orders_2)).
% 0.14/0.38  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.14/0.38  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.14/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2)))))), inference(assume_negation,[status(cth)],[t24_yellow_0])).
% 0.14/0.38  fof(c_0_7, plain, ![X12, X13, X14, X15]:((~v6_orders_2(X15,X12)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))|~r2_hidden(X13,X15)|~r2_hidden(X14,X15)|r1_orders_2(X12,X13,X14)|r1_orders_2(X12,X14,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12)))&((((v6_orders_2(esk1_3(X12,X13,X14),X12)|~r1_orders_2(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12)))&(m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))|~r1_orders_2(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12))))&((r2_hidden(X13,esk1_3(X12,X13,X14))|~r1_orders_2(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12)))&(r2_hidden(X14,esk1_3(X12,X13,X14))|~r1_orders_2(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12)))))&(((v6_orders_2(esk1_3(X12,X13,X14),X12)|~r1_orders_2(X12,X14,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12)))&(m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))|~r1_orders_2(X12,X14,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12))))&((r2_hidden(X13,esk1_3(X12,X13,X14))|~r1_orders_2(X12,X14,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12)))&(r2_hidden(X14,esk1_3(X12,X13,X14))|~r1_orders_2(X12,X14,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(~v3_orders_2(X12)|~l1_orders_2(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ((((v3_orders_2(esk2_0)&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((esk3_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0))&(esk3_0=k13_lattice3(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X10, X11]:(v2_struct_0(X10)|~v3_orders_2(X10)|~l1_orders_2(X10)|(~m1_subset_1(X11,u1_struct_0(X10))|r1_orders_2(X10,X11,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.14/0.38  cnf(c_0_10, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  fof(c_0_14, plain, ![X8]:(~v2_struct_0(X8)|~l1_struct_0(X8)|v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.14/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  fof(c_0_17, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (esk3_0=k13_lattice3(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_20, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)|v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  fof(c_0_22, plain, ![X9]:(~l1_orders_2(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_27, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_28, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_34, plain, (v6_orders_2(esk1_3(X1,X2,X3),X1)|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_35, plain, (r2_hidden(X1,esk1_3(X2,X1,X3))|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_36, plain, (v6_orders_2(esk1_3(X1,X2,X3),X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_37, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_38, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_39, plain, (r2_hidden(X1,esk1_3(X2,X1,X3))|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,esk3_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,esk4_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.14/0.38  cnf(c_0_43, plain, (r1_orders_2(X2,X3,X4)|r1_orders_2(X2,X4,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~r2_hidden(X4,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['final']).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_41]), ['final']).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk2_0,X1,esk3_0)|r1_orders_2(esk2_0,esk3_0,X1)|~v6_orders_2(X2,esk2_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk3_0,X2)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_19]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_19]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_19]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_19]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_19]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|r1_orders_2(esk2_0,esk4_0,X1)|~v6_orders_2(X2,esk2_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk4_0,X2)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_19]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk3_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_51]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_51]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_66, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk4_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_53]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_53]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_69, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_25]), ['final']).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_58]), c_0_59]), c_0_60]), ['final']).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_41]), c_0_25]), ['final']).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_58]), c_0_62]), c_0_60]), ['final']).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_63]), c_0_64]), c_0_65]), ['final']).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk4_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_66]), c_0_67]), ['final']).
% 0.14/0.38  cnf(c_0_75, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk3_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_63]), c_0_65]), ['final']).
% 0.14/0.38  cnf(c_0_76, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_66]), c_0_68]), c_0_67]), ['final']).
% 0.14/0.38  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_78, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_60]), ['final']).
% 0.14/0.38  cnf(c_0_79, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_80, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_81, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_65]), ['final']).
% 0.14/0.38  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_83, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_67]), ['final']).
% 0.14/0.38  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_16]), c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_85, negated_conjecture, (esk3_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_86, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_87, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 88
% 0.14/0.38  # Proof object clause steps            : 75
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 65
% 0.14/0.38  # Proof object clause conjectures      : 62
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 21
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 54
% 0.14/0.38  # Proof object simplifying inferences  : 106
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 21
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 21
% 0.14/0.38  # Processed clauses                    : 124
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 28
% 0.14/0.38  # ...remaining for further processing  : 96
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 4
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 82
% 0.14/0.38  # ...of the previous two non-trivial   : 82
% 0.14/0.38  # Contextual simplify-reflections      : 14
% 0.14/0.38  # Paramodulations                      : 82
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 71
% 0.14/0.38  #    Positive orientable unit clauses  : 6
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 65
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 25
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1305
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 177
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 46
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4393
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.036 s
% 0.14/0.38  # System time              : 0.001 s
% 0.14/0.38  # Total time               : 0.037 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
