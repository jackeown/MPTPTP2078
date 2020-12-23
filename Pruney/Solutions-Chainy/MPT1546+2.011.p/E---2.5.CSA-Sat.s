%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:17 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  104 (2214 expanded)
%              Number of clauses        :   89 ( 766 expanded)
%              Number of leaves         :    7 ( 527 expanded)
%              Depth                    :   14
%              Number of atoms          :  457 (17348 expanded)
%              Number of equality atoms :   45 (1742 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ v6_orders_2(X19,X16)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X18,X19)
        | r1_orders_2(X16,X17,X18)
        | r1_orders_2(X16,X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( v6_orders_2(esk1_3(X16,X17,X18),X16)
        | ~ r1_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r1_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(X17,esk1_3(X16,X17,X18))
        | ~ r1_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(X18,esk1_3(X16,X17,X18))
        | ~ r1_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( v6_orders_2(esk1_3(X16,X17,X18),X16)
        | ~ r1_orders_2(X16,X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r1_orders_2(X16,X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(X17,esk1_3(X16,X17,X18))
        | ~ r1_orders_2(X16,X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(X18,esk1_3(X16,X17,X18))
        | ~ r1_orders_2(X16,X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v3_orders_2(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).

fof(c_0_9,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( esk3_0 = k13_lattice3(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_18,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v3_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | r3_orders_2(X13,X14,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),
    [final]).

fof(c_0_21,plain,(
    ! [X8] :
      ( ~ v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_22,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r3_orders_2(X10,X11,X12)
        | r1_orders_2(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) )
      & ( ~ r1_orders_2(X10,X11,X12)
        | r3_orders_2(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_25,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

fof(c_0_26,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r3_orders_2(esk2_0,X1,X1)
    | v2_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ l1_struct_0(esk2_0)
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk3_0)
    | v2_struct_0(esk2_0)
    | ~ r3_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r3_orders_2(esk2_0,esk3_0,esk3_0)
    | v2_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17]),
    [final]).

cnf(c_0_33,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | v2_struct_0(esk2_0)
    | ~ r3_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r3_orders_2(esk2_0,esk4_0,esk4_0)
    | v2_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_11]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13])]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_11])]),
    [final]).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,esk3_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_11])]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42]),
    [final]).

cnf(c_0_48,plain,
    ( v6_orders_2(esk1_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_49,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_50,plain,
    ( v6_orders_2(esk1_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_51,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_52,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_11])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_17])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | m1_subset_1(esk1_3(esk2_0,esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_47]),c_0_11])]),
    [final]).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_53]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_54]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_55]),
    [final]).

cnf(c_0_67,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,X1)
    | ~ v6_orders_2(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk3_0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_16]),c_0_17])]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_17])]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_16]),c_0_11])]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_16]),c_0_17])]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,X1)
    | ~ v6_orders_2(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk3_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_46]),c_0_17])]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_17])]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | v6_orders_2(esk1_3(esk2_0,esk4_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47]),c_0_11])]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_47]),c_0_11])]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_16]),c_0_11])]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ l1_struct_0(esk2_0)
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_25])).

cnf(c_0_80,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ l1_struct_0(esk2_0)
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ l1_struct_0(esk2_0)
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_25])).

cnf(c_0_82,negated_conjecture,
    ( r3_orders_2(esk2_0,X1,esk3_0)
    | v2_struct_0(esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_20]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_71]),c_0_72]),c_0_53]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_69]),c_0_42]),c_0_20]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_74]),c_0_75]),c_0_54]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,X1)
    | r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_76]),c_0_55]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_54]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_76]),c_0_77]),c_0_55]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_71]),c_0_78]),c_0_53]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_30]),c_0_13])]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_30]),c_0_13])]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ v2_struct_0(esk2_0)
    | ~ r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_30]),c_0_13])]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r3_orders_2(esk2_0,esk4_0,esk3_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_16]),c_0_11])]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( r3_orders_2(esk2_0,X1,esk4_0)
    | v2_struct_0(esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_11]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_17]),c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( esk3_0 != k13_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.38  # and selection function SelectNewComplexAHP.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # No proof found!
% 0.19/0.38  # SZS status CounterSatisfiable
% 0.19/0.38  # SZS output start Saturation
% 0.19/0.38  fof(t24_yellow_0, conjecture, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_0)).
% 0.19/0.38  fof(t38_orders_2, axiom, ![X1]:((v3_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(~(((?[X4]:(((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))&r2_hidden(X2,X4))&r2_hidden(X3,X4))&~(r1_orders_2(X1,X2,X3)))&~(r1_orders_2(X1,X3,X2))))&~(((r1_orders_2(X1,X2,X3)|r1_orders_2(X1,X3,X2))&![X4]:((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~((r2_hidden(X2,X4)&r2_hidden(X3,X4)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_orders_2)).
% 0.19/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.38  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.19/0.38  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.19/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2)))))), inference(assume_negation,[status(cth)],[t24_yellow_0])).
% 0.19/0.38  fof(c_0_8, plain, ![X16, X17, X18, X19]:((~v6_orders_2(X19,X16)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|~r2_hidden(X17,X19)|~r2_hidden(X18,X19)|r1_orders_2(X16,X17,X18)|r1_orders_2(X16,X18,X17)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16)))&((((v6_orders_2(esk1_3(X16,X17,X18),X16)|~r1_orders_2(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16)))&(m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))|~r1_orders_2(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16))))&((r2_hidden(X17,esk1_3(X16,X17,X18))|~r1_orders_2(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16)))&(r2_hidden(X18,esk1_3(X16,X17,X18))|~r1_orders_2(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16)))))&(((v6_orders_2(esk1_3(X16,X17,X18),X16)|~r1_orders_2(X16,X18,X17)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16)))&(m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))|~r1_orders_2(X16,X18,X17)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16))))&((r2_hidden(X17,esk1_3(X16,X17,X18))|~r1_orders_2(X16,X18,X17)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16)))&(r2_hidden(X18,esk1_3(X16,X17,X18))|~r1_orders_2(X16,X18,X17)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(~v3_orders_2(X16)|~l1_orders_2(X16))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ((((v3_orders_2(esk2_0)&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((esk3_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0))&(esk3_0=k13_lattice3(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.38  cnf(c_0_10, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  cnf(c_0_12, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  fof(c_0_14, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (esk3_0=k13_lattice3(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  fof(c_0_18, plain, ![X13, X14, X15]:(v2_struct_0(X13)|~v3_orders_2(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|r3_orders_2(X13,X14,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.19/0.38  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), ['final']).
% 0.19/0.38  fof(c_0_21, plain, ![X8]:(~v2_struct_0(X8)|~l1_struct_0(X8)|v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.19/0.38  fof(c_0_22, plain, ![X10, X11, X12]:((~r3_orders_2(X10,X11,X12)|r1_orders_2(X10,X11,X12)|(v2_struct_0(X10)|~v3_orders_2(X10)|~l1_orders_2(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))))&(~r1_orders_2(X10,X11,X12)|r3_orders_2(X10,X11,X12)|(v2_struct_0(X10)|~v3_orders_2(X10)|~l1_orders_2(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.38  cnf(c_0_23, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.19/0.38  cnf(c_0_25, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.19/0.38  fof(c_0_26, plain, ![X9]:(~l1_orders_2(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.38  cnf(c_0_27, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r3_orders_2(esk2_0,X1,X1)|v2_struct_0(esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~l1_struct_0(esk2_0)|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk2_0,X1,esk3_0)|v2_struct_0(esk2_0)|~r3_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (r3_orders_2(esk2_0,esk3_0,esk3_0)|v2_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_33, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|v2_struct_0(esk2_0)|~r3_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r3_orders_2(esk2_0,esk4_0,esk4_0)|v2_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_11]), ['final']).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)|v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_17])]), ['final']).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_40, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,esk3_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,esk4_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_39])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_42]), ['final']).
% 0.19/0.38  cnf(c_0_48, plain, (v6_orders_2(esk1_3(X1,X2,X3),X1)|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_49, plain, (r2_hidden(X1,esk1_3(X2,X1,X3))|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_50, plain, (v6_orders_2(esk1_3(X1,X2,X3),X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_51, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_52, plain, (r2_hidden(X1,esk1_3(X2,X1,X3))|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_17])]), ['final']).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|m1_subset_1(esk1_3(esk2_0,esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_47]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_56, plain, (r1_orders_2(X2,X3,X4)|r1_orders_2(X2,X4,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~r2_hidden(X4,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk4_0),esk2_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_53]), ['final']).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_54]), ['final']).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_55]), ['final']).
% 0.19/0.38  cnf(c_0_67, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk2_0,X1,esk3_0)|r1_orders_2(esk2_0,esk3_0,X1)|~v6_orders_2(X2,esk2_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk3_0,X2)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_16]), c_0_17])]), ['final']).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_16]), c_0_17])]), ['final']).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_16]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_16]), c_0_17])]), ['final']).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|r1_orders_2(esk2_0,esk4_0,X1)|~v6_orders_2(X2,esk2_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk4_0,X2)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk3_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_46]), c_0_17])]), ['final']).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_46]), c_0_17])]), ['final']).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|v6_orders_2(esk1_3(esk2_0,esk4_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_47]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_16]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~l1_struct_0(esk2_0)|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_25])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~l1_struct_0(esk2_0)|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_25])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~l1_struct_0(esk2_0)|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_25])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (r3_orders_2(esk2_0,X1,esk3_0)|v2_struct_0(esk2_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_20]), ['final']).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_71]), c_0_72]), c_0_53]), ['final']).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_69]), c_0_42]), c_0_20]), ['final']).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_74]), c_0_75]), c_0_54]), ['final']).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk3_0,X1)|r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk4_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_76]), c_0_55]), ['final']).
% 0.19/0.38  cnf(c_0_88, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk3_0))|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_54]), ['final']).
% 0.19/0.38  cnf(c_0_89, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_76]), c_0_77]), c_0_55]), ['final']).
% 0.19/0.38  cnf(c_0_90, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_71]), c_0_78]), c_0_53]), ['final']).
% 0.19/0.38  cnf(c_0_91, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk4_0))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_92, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_30]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_93, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_30]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_94, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_95, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~v2_struct_0(esk2_0)|~r2_hidden(X1,esk1_3(esk2_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_30]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_97, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_98, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r3_orders_2(esk2_0,esk4_0,esk3_0)|v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_16]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_99, negated_conjecture, (r3_orders_2(esk2_0,X1,esk4_0)|v2_struct_0(esk2_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_11]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_100, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_17]), c_0_12]), c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_101, negated_conjecture, (esk3_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  cnf(c_0_102, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  cnf(c_0_103, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  # SZS output end Saturation
% 0.19/0.38  # Proof object total steps             : 104
% 0.19/0.38  # Proof object clause steps            : 89
% 0.19/0.38  # Proof object formula steps           : 15
% 0.19/0.38  # Proof object conjectures             : 77
% 0.19/0.38  # Proof object clause conjectures      : 74
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 7
% 0.19/0.38  # Proof object generating inferences   : 66
% 0.19/0.38  # Proof object simplifying inferences  : 125
% 0.19/0.38  # Parsed axioms                        : 7
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 23
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 23
% 0.19/0.38  # Processed clauses                    : 144
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 32
% 0.19/0.38  # ...remaining for further processing  : 112
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 6
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 98
% 0.19/0.38  # ...of the previous two non-trivial   : 98
% 0.19/0.38  # Contextual simplify-reflections      : 14
% 0.19/0.38  # Paramodulations                      : 98
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 83
% 0.19/0.38  #    Positive orientable unit clauses  : 6
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 77
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 29
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2072
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 322
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 52
% 0.19/0.38  # Unit Clause-clause subsumption calls : 0
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5314
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
