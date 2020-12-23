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
% DateTime   : Thu Dec  3 11:16:05 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   70 (1250 expanded)
%              Number of clauses        :   55 ( 521 expanded)
%              Number of leaves         :    7 ( 294 expanded)
%              Depth                    :   11
%              Number of atoms          :  248 (5793 expanded)
%              Number of equality atoms :   53 (1758 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t3_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( X3 = X4
                        & v1_waybel_0(X3,X1) )
                     => v1_waybel_0(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(t60_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X2,X5,X6) )
                           => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | g1_orders_2(X13,X14) != g1_orders_2(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))) )
      & ( X14 = X16
        | g1_orders_2(X13,X14) != g1_orders_2(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_8,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(u1_orders_2(X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X12)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( ( X3 = X4
                          & v1_waybel_0(X3,X1) )
                       => v1_waybel_0(X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_waybel_0])).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_12,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk3_0 = esk4_0
    & v1_waybel_0(esk3_0,esk1_0)
    & ~ v1_waybel_0(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( u1_orders_2(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_17,negated_conjecture,
    ( u1_orders_2(esk2_0) = u1_orders_2(esk1_0) ),
    inference(er,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_17]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_17])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(u1_struct_0(X18),u1_struct_0(X17))
        | ~ m1_yellow_0(X18,X17)
        | ~ l1_orders_2(X18)
        | ~ l1_orders_2(X17) )
      & ( r1_tarski(u1_orders_2(X18),u1_orders_2(X17))
        | ~ m1_yellow_0(X18,X17)
        | ~ l1_orders_2(X18)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_tarski(u1_struct_0(X18),u1_struct_0(X17))
        | ~ r1_tarski(u1_orders_2(X18),u1_orders_2(X17))
        | m1_yellow_0(X18,X17)
        | ~ l1_orders_2(X18)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ~ l1_orders_2(X19)
      | ~ m1_yellow_0(X20,X19)
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ m1_subset_1(X22,u1_struct_0(X19))
      | ~ m1_subset_1(X23,u1_struct_0(X20))
      | ~ m1_subset_1(X24,u1_struct_0(X20))
      | X23 != X21
      | X24 != X22
      | ~ r1_orders_2(X20,X23,X24)
      | r1_orders_2(X19,X21,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_yellow_0])])])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_26,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

fof(c_0_27,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_28,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X5 != X3
    | X6 != X4
    | ~ r1_orders_2(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( u1_orders_2(X1) = u1_orders_2(X2)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(u1_orders_2(esk1_0),u1_orders_2(X1))
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_15])]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_orders_2(esk1_0),u1_orders_2(X1))
    | ~ r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_15])]),c_0_29]),
    [final]).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_yellow_0(X4,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( m1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(esk1_0))
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_15])]),c_0_29]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(esk1_0))
    | ~ m1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_15])]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk1_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_15])]),
    [final]).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_11]),
    [final]).

cnf(c_0_43,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( m1_yellow_0(esk1_0,X1)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_35])]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_35]),c_0_37])]),
    [final]).

cnf(c_0_49,plain,
    ( m1_yellow_0(X1,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_37]),c_0_37])]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(esk2_0,X2,X3)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( u1_orders_2(esk1_0) = u1_orders_2(X1)
    | ~ m1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_orders_2(esk1_0),u1_orders_2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_15])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( m1_yellow_0(X1,esk2_0)
    | ~ m1_yellow_0(X1,esk1_0)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_35])]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( m1_yellow_0(esk2_0,X1)
    | ~ m1_yellow_0(esk1_0,X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_35])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( m1_yellow_0(X1,esk1_0)
    | ~ m1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_40]),c_0_35])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk1_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ m1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk1_0)
    | ~ m1_yellow_0(esk1_0,X1)
    | ~ m1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_35])]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( u1_orders_2(esk1_0) = u1_orders_2(X1)
    | ~ m1_yellow_0(X1,esk1_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_34]),c_0_35])]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_17]),c_0_15])]),c_0_29]),c_0_29]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_17]),c_0_20]),c_0_15])]),c_0_29]),
    [final]).

cnf(c_0_60,plain,
    ( u1_orders_2(X1) = u1_orders_2(X2)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( u1_orders_2(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_44]),
    [final]).

cnf(c_0_63,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( m1_yellow_0(esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_37])]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( m1_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_49]),c_0_15]),c_0_29]),c_0_37])]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_17]),c_0_15]),c_0_37]),c_0_29]),c_0_37])]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_29]),c_0_29]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( v1_waybel_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.13/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.13/0.38  fof(t3_waybel_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((X3=X4&v1_waybel_0(X3,X1))=>v1_waybel_0(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_waybel_0)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(d13_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(m1_yellow_0(X2,X1)<=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X1))&r1_tarski(u1_orders_2(X2),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 0.13/0.38  fof(t60_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(((X5=X3&X6=X4)&r1_orders_2(X2,X5,X6))=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_yellow_0)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(c_0_7, plain, ![X13, X14, X15, X16]:((X13=X15|g1_orders_2(X13,X14)!=g1_orders_2(X15,X16)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))))&(X14=X16|g1_orders_2(X13,X14)!=g1_orders_2(X15,X16)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X12]:(~l1_orders_2(X12)|m1_subset_1(u1_orders_2(X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X12))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((X3=X4&v1_waybel_0(X3,X1))=>v1_waybel_0(X4,X2)))))))), inference(assume_negation,[status(cth)],[t3_waybel_0])).
% 0.13/0.38  cnf(c_0_10, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_11, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  fof(c_0_12, negated_conjecture, (l1_orders_2(esk1_0)&(l1_orders_2(esk2_0)&(g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((esk3_0=esk4_0&v1_waybel_0(esk3_0,esk1_0))&~v1_waybel_0(esk4_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  cnf(c_0_13, plain, (u1_orders_2(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X3,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (u1_orders_2(esk2_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (u1_orders_2(esk2_0)=u1_orders_2(esk1_0)), inference(er,[status(thm)],[c_0_16]), ['final']).
% 0.13/0.38  cnf(c_0_18, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_17]), c_0_15])])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))), inference(rw,[status(thm)],[c_0_14, c_0_17])).
% 0.13/0.38  fof(c_0_21, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X17, X18]:(((r1_tarski(u1_struct_0(X18),u1_struct_0(X17))|~m1_yellow_0(X18,X17)|~l1_orders_2(X18)|~l1_orders_2(X17))&(r1_tarski(u1_orders_2(X18),u1_orders_2(X17))|~m1_yellow_0(X18,X17)|~l1_orders_2(X18)|~l1_orders_2(X17)))&(~r1_tarski(u1_struct_0(X18),u1_struct_0(X17))|~r1_tarski(u1_orders_2(X18),u1_orders_2(X17))|m1_yellow_0(X18,X17)|~l1_orders_2(X18)|~l1_orders_2(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (u1_struct_0(esk2_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.13/0.38  fof(c_0_24, plain, ![X19, X20, X21, X22, X23, X24]:(~l1_orders_2(X19)|(~m1_yellow_0(X20,X19)|(~m1_subset_1(X21,u1_struct_0(X19))|(~m1_subset_1(X22,u1_struct_0(X19))|(~m1_subset_1(X23,u1_struct_0(X20))|(~m1_subset_1(X24,u1_struct_0(X20))|(X23!=X21|X24!=X22|~r1_orders_2(X20,X23,X24)|r1_orders_2(X19,X21,X22)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_yellow_0])])])).
% 0.13/0.38  cnf(c_0_25, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.13/0.38  fof(c_0_27, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_yellow_0(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk1_0)), inference(er,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_orders_2(X1,X3,X4)|~l1_orders_2(X1)|~m1_yellow_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X2))|X5!=X3|X6!=X4|~r1_orders_2(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_32, plain, (u1_orders_2(X1)=u1_orders_2(X2)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)|~l1_orders_2(X2)|~r1_tarski(u1_orders_2(X1),u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.13/0.38  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(u1_orders_2(esk1_0),u1_orders_2(X1))|~m1_yellow_0(esk2_0,X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_15])]), ['final']).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_yellow_0(esk2_0,X1)|~l1_orders_2(X1)|~r1_tarski(u1_orders_2(esk1_0),u1_orders_2(X1))|~r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_15])]), c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30]), ['final']).
% 0.13/0.38  cnf(c_0_38, plain, (r1_orders_2(X1,X2,X3)|~r1_orders_2(X4,X2,X3)|~m1_yellow_0(X4,X1)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])]), ['final']).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (m1_yellow_0(X1,esk2_0)|~l1_orders_2(X1)|~r1_tarski(u1_orders_2(X1),u1_orders_2(esk1_0))|~r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_15])]), c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(u1_orders_2(X1),u1_orders_2(esk1_0))|~m1_yellow_0(X1,esk2_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_15])]), ['final']).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (u1_orders_2(X1)=u1_orders_2(esk1_0)|~m1_yellow_0(esk2_0,X1)|~l1_orders_2(X1)|~r1_tarski(u1_orders_2(X1),u1_orders_2(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_15])]), ['final']).
% 0.13/0.38  cnf(c_0_42, plain, (m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))|~l1_orders_2(X2)|~r2_hidden(X1,u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_33, c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_43, plain, (u1_struct_0(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X2,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~v1_waybel_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk3_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (m1_yellow_0(esk1_0,X1)|~m1_yellow_0(esk2_0,X1)|~l1_orders_2(X1)|~r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_34]), c_0_35])]), ['final']).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (m1_yellow_0(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_35]), c_0_37])]), ['final']).
% 0.13/0.38  cnf(c_0_49, plain, (m1_yellow_0(X1,X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_37]), c_0_37])]), ['final']).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_orders_2(X1,X2,X3)|~r1_orders_2(esk2_0,X2,X3)|~m1_yellow_0(esk2_0,X1)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (u1_orders_2(esk1_0)=u1_orders_2(X1)|~m1_yellow_0(X1,esk2_0)|~l1_orders_2(X1)|~r1_tarski(u1_orders_2(esk1_0),u1_orders_2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_15])]), ['final']).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (m1_yellow_0(X1,esk2_0)|~m1_yellow_0(X1,esk1_0)|~l1_orders_2(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_35])]), ['final']).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_yellow_0(esk2_0,X1)|~m1_yellow_0(esk1_0,X1)|~l1_orders_2(X1)|~r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_35])]), ['final']).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (m1_yellow_0(X1,esk1_0)|~m1_yellow_0(X1,esk2_0)|~l1_orders_2(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_40]), c_0_35])]), ['final']).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (u1_orders_2(X1)=u1_orders_2(esk1_0)|~m1_yellow_0(esk2_0,X1)|~m1_yellow_0(X1,esk2_0)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (u1_orders_2(X1)=u1_orders_2(esk1_0)|~m1_yellow_0(esk1_0,X1)|~m1_yellow_0(X1,esk2_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_40]), c_0_35])]), ['final']).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (u1_orders_2(esk1_0)=u1_orders_2(X1)|~m1_yellow_0(X1,esk1_0)|~m1_yellow_0(esk2_0,X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_34]), c_0_35])]), ['final']).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))|~r2_hidden(X1,u1_orders_2(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_17]), c_0_15])]), c_0_29]), c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk1_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_17]), c_0_20]), c_0_15])]), c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_60, plain, (u1_orders_2(X1)=u1_orders_2(X2)|~m1_yellow_0(X2,X1)|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_32, c_0_26]), ['final']).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (u1_orders_2(esk1_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X2,X1)), inference(rw,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk1_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_44]), ['final']).
% 0.13/0.38  cnf(c_0_63, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (~v1_waybel_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_45, c_0_46]), ['final']).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (m1_yellow_0(esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_37])]), ['final']).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (m1_yellow_0(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_49]), c_0_15]), c_0_29]), c_0_37])]), ['final']).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (m1_yellow_0(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_17]), c_0_15]), c_0_37]), c_0_29]), c_0_37])]), ['final']).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_29]), c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (v1_waybel_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 70
% 0.13/0.38  # Proof object clause steps            : 55
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 40
% 0.13/0.38  # Proof object clause conjectures      : 37
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 32
% 0.13/0.38  # Proof object simplifying inferences  : 64
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 95
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 17
% 0.13/0.38  # ...remaining for further processing  : 75
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 7
% 0.13/0.38  # Generated clauses                    : 93
% 0.13/0.38  # ...of the previous two non-trivial   : 62
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 84
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 10
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 47
% 0.13/0.38  #    Positive orientable unit clauses  : 13
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 33
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 25
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 168
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 67
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 17
% 0.13/0.38  # Unit Clause-clause subsumption calls : 1
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3467
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
