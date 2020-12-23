%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1922+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   37 (  83 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 619 expanded)
%              Number of equality atoms :   17 ( 103 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t20_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X3))
                             => ( ( X4 = X6
                                  & X5 = X7
                                  & r1_orders_2(X3,X6,X7) )
                               => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_6)).

fof(d8_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( l1_waybel_0(X3,X1)
             => ( m1_yellow_6(X3,X1,X2)
              <=> ( m1_yellow_0(X3,X2)
                  & u1_waybel_0(X1,X3) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ~ l1_orders_2(X16)
      | ~ m1_yellow_0(X17,X16)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X19,u1_struct_0(X16))
      | ~ m1_subset_1(X20,u1_struct_0(X17))
      | ~ m1_subset_1(X21,u1_struct_0(X17))
      | X20 != X18
      | X21 != X19
      | ~ r1_orders_2(X17,X20,X21)
      | r1_orders_2(X16,X18,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_yellow_0])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_waybel_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_6(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X4 = X6
                                    & X5 = X7
                                    & r1_orders_2(X3,X6,X7) )
                                 => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_yellow_6])).

cnf(c_0_7,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_yellow_6(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk4_0 = esk6_0
    & esk5_0 = esk7_0
    & r1_orders_2(esk3_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ( m1_yellow_0(X10,X9)
        | ~ m1_yellow_6(X10,X8,X9)
        | ~ l1_waybel_0(X10,X8)
        | ~ l1_waybel_0(X9,X8)
        | ~ l1_struct_0(X8) )
      & ( u1_waybel_0(X8,X10) = k2_partfun1(u1_struct_0(X9),u1_struct_0(X8),u1_waybel_0(X8,X9),u1_struct_0(X10))
        | ~ m1_yellow_6(X10,X8,X9)
        | ~ l1_waybel_0(X10,X8)
        | ~ l1_waybel_0(X9,X8)
        | ~ l1_struct_0(X8) )
      & ( ~ m1_yellow_0(X10,X9)
        | u1_waybel_0(X8,X10) != k2_partfun1(u1_struct_0(X9),u1_struct_0(X8),u1_waybel_0(X8,X9),u1_struct_0(X10))
        | m1_yellow_6(X10,X8,X9)
        | ~ l1_waybel_0(X10,X8)
        | ~ l1_waybel_0(X9,X8)
        | ~ l1_struct_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ~ l1_struct_0(X13)
      | ~ l1_waybel_0(X14,X13)
      | ~ m1_yellow_6(X15,X13,X14)
      | l1_waybel_0(X15,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

cnf(c_0_11,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X4,X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ l1_struct_0(X11)
      | ~ l1_waybel_0(X12,X11)
      | l1_orders_2(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_17,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(X1,X2,esk7_0)
    | ~ r1_orders_2(esk3_0,X2,esk7_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_22,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( esk5_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( m1_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(X1,esk4_0,esk7_0)
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk4_0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_31,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_24])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35])]),
    [proof]).

%------------------------------------------------------------------------------
