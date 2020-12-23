%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 153 expanded)
%              Number of clauses        :   22 (  46 expanded)
%              Number of leaves         :    3 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 (1540 expanded)
%              Number of equality atoms :   17 ( 216 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & v4_waybel_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( ( v1_waybel_0(X3,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
             => ( r1_yellow_0(X1,X3)
               => ( X3 = k1_xboole_0
                  | ( r1_yellow_0(X2,X3)
                    & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_0)).

fof(d4_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_waybel_0(X2,X1)
          <=> ! [X3] :
                ( ( v1_waybel_0(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
               => ( r1_yellow_0(X1,X3)
                 => ( X3 = k1_xboole_0
                    | r2_hidden(k1_yellow_0(X1,X3),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_waybel_0)).

fof(t65_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r1_yellow_0(X1,X3)
                  & r2_hidden(k1_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r1_yellow_0(X2,X3)
                  & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v4_waybel_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( ( v1_waybel_0(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
               => ( r1_yellow_0(X1,X3)
                 => ( X3 = k1_xboole_0
                    | ( r1_yellow_0(X2,X3)
                      & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_waybel_0])).

fof(c_0_4,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v4_waybel_0(X5,X4)
        | ~ v1_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r1_yellow_0(X4,X6)
        | X6 = k1_xboole_0
        | r2_hidden(k1_yellow_0(X4,X6),u1_struct_0(X5))
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_orders_2(X4) )
      & ( v1_waybel_0(esk1_2(X4,X5),X5)
        | v4_waybel_0(X5,X4)
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_orders_2(X4) )
      & ( m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(u1_struct_0(X5)))
        | v4_waybel_0(X5,X4)
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_orders_2(X4) )
      & ( r1_yellow_0(X4,esk1_2(X4,X5))
        | v4_waybel_0(X5,X4)
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_orders_2(X4) )
      & ( esk1_2(X4,X5) != k1_xboole_0
        | v4_waybel_0(X5,X4)
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_orders_2(X4) )
      & ( ~ r2_hidden(k1_yellow_0(X4,esk1_2(X4,X5)),u1_struct_0(X5))
        | v4_waybel_0(X5,X4)
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_waybel_0])])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v4_yellow_0(esk3_0,esk2_0)
    & v4_waybel_0(esk3_0,esk2_0)
    & m1_yellow_0(esk3_0,esk2_0)
    & v1_waybel_0(esk4_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r1_yellow_0(esk2_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & ( ~ r1_yellow_0(esk3_0,esk4_0)
      | k1_yellow_0(esk3_0,esk4_0) != k1_yellow_0(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X8,X9,X10] :
      ( ( r1_yellow_0(X9,X10)
        | ~ r1_yellow_0(X8,X10)
        | ~ r2_hidden(k1_yellow_0(X8,X10),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v4_yellow_0(X9,X8)
        | ~ m1_yellow_0(X9,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( k1_yellow_0(X9,X10) = k1_yellow_0(X8,X10)
        | ~ r1_yellow_0(X8,X10)
        | ~ r2_hidden(k1_yellow_0(X8,X10),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v4_yellow_0(X9,X8)
        | ~ m1_yellow_0(X9,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_yellow_0])])])])])).

cnf(c_0_7,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X2,X3),u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ v4_waybel_0(X1,X2)
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_yellow_0(X3,X2)
    | ~ r2_hidden(k1_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k1_yellow_0(X1,esk4_0),u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,esk4_0)
    | ~ v4_waybel_0(esk3_0,X1)
    | ~ m1_yellow_0(esk3_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v4_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v4_yellow_0(esk3_0,X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(k1_yellow_0(X1,esk4_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(X1,esk4_0)
    | ~ m1_yellow_0(esk3_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v4_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk2_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_yellow_0(X3,X2)
    | ~ r2_hidden(k1_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_yellow_0(esk3_0,esk4_0)
    | k1_yellow_0(esk3_0,esk4_0) != k1_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_14]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk4_0) = k1_yellow_0(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ v4_yellow_0(esk3_0,X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(k1_yellow_0(X1,esk4_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(X1,esk4_0)
    | ~ m1_yellow_0(esk3_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_8]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk4_0) != k1_yellow_0(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22]),c_0_14]),c_0_16]),c_0_17])]),c_0_27]),c_0_18]),
    [proof]).

%------------------------------------------------------------------------------
