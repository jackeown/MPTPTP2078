%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  155 (36546665 expanded)
%              Number of clauses        :  146 (11657406 expanded)
%              Number of leaves         :    4 (8829633 expanded)
%              Depth                    :   24
%              Number of atoms          :  744 (577191615 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   62 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v4_orders_2(X3)
                  & v7_waybel_0(X3)
                  & v3_yellow_6(X3,X1)
                  & l1_waybel_0(X3,X1) )
               => ( r1_waybel_0(X1,X3,X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,k10_yellow_6(X1,X3))
                       => r2_hidden(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow19)).

fof(t25_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v4_orders_2(X3)
                  & v7_waybel_0(X3)
                  & l1_waybel_0(X3,X1) )
               => ( r1_waybel_0(X1,X3,X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r3_waybel_9(X1,X3,X4)
                       => r2_hidden(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow19)).

fof(t23_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ? [X4] :
                    ( ~ v2_struct_0(X4)
                    & v4_orders_2(X4)
                    & v7_waybel_0(X4)
                    & l1_waybel_0(X4,X1)
                    & r1_waybel_0(X1,X4,X2)
                    & r3_waybel_9(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).

fof(t24_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ? [X4] :
                    ( ~ v2_struct_0(X4)
                    & v4_orders_2(X4)
                    & v7_waybel_0(X4)
                    & v3_yellow_6(X4,X1)
                    & l1_waybel_0(X4,X1)
                    & r1_waybel_0(X1,X4,X2)
                    & r2_hidden(X3,k10_yellow_6(X1,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow19)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v4_orders_2(X3)
                    & v7_waybel_0(X3)
                    & v3_yellow_6(X3,X1)
                    & l1_waybel_0(X3,X1) )
                 => ( r1_waybel_0(X1,X3,X2)
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r2_hidden(X4,k10_yellow_6(X1,X3))
                         => r2_hidden(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_yellow19])).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ v4_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ v4_orders_2(X17)
        | ~ v7_waybel_0(X17)
        | ~ l1_waybel_0(X17,X15)
        | ~ r1_waybel_0(X15,X17,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r3_waybel_9(X15,X17,X18)
        | r2_hidden(X18,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ v2_struct_0(esk3_2(X15,X16))
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v4_orders_2(esk3_2(X15,X16))
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v7_waybel_0(esk3_2(X15,X16))
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( l1_waybel_0(esk3_2(X15,X16),X15)
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r1_waybel_0(X15,esk3_2(X15,X16),X16)
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk4_2(X15,X16),u1_struct_0(X15))
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r3_waybel_9(X15,esk3_2(X15,X16),esk4_2(X15,X16))
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow19])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X25,X26] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & ( ~ v2_struct_0(esk7_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v4_orders_2(esk7_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v7_waybel_0(esk7_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v3_yellow_6(esk7_0,esk5_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( l1_waybel_0(esk7_0,esk5_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( r1_waybel_0(esk5_0,esk7_0,esk6_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( ~ r2_hidden(esk8_0,esk6_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v4_pre_topc(esk6_0,esk5_0)
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ v3_yellow_6(X25,esk5_0)
        | ~ l1_waybel_0(X25,esk5_0)
        | ~ r1_waybel_0(esk5_0,X25,esk6_0)
        | ~ m1_subset_1(X26,u1_struct_0(esk5_0))
        | ~ r2_hidden(X26,k10_yellow_6(esk5_0,X25))
        | r2_hidden(X26,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X9] :
      ( ( ~ v2_struct_0(esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v4_orders_2(esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v7_waybel_0(esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( l1_waybel_0(esk1_3(X5,X6,X7),X5)
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r1_waybel_0(X5,esk1_3(X5,X6,X7),X6)
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r3_waybel_9(X5,esk1_3(X5,X6,X7),X7)
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X5)
        | ~ r1_waybel_0(X5,X9,X6)
        | ~ r3_waybel_9(X5,X9,X7)
        | r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_yellow19])])])])])])).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X14] :
      ( ( ~ v2_struct_0(esk2_3(X10,X11,X12))
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v4_orders_2(esk2_3(X10,X11,X12))
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v7_waybel_0(esk2_3(X10,X11,X12))
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_yellow_6(esk2_3(X10,X11,X12),X10)
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( l1_waybel_0(esk2_3(X10,X11,X12),X10)
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r1_waybel_0(X10,esk2_3(X10,X11,X12),X11)
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(X12,k10_yellow_6(X10,esk2_3(X10,X11,X12)))
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v2_struct_0(X14)
        | ~ v4_orders_2(X14)
        | ~ v7_waybel_0(X14)
        | ~ v3_yellow_6(X14,X10)
        | ~ l1_waybel_0(X14,X10)
        | ~ r1_waybel_0(X10,X14,X11)
        | ~ r2_hidden(X12,k10_yellow_6(X10,X14))
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_yellow19])])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X4,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ r1_waybel_0(X2,X1,X3)
    | ~ r3_waybel_9(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_waybel_0(X1,esk3_2(X1,X2),X2)
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( v4_orders_2(esk3_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( v7_waybel_0(esk3_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( l1_waybel_0(esk3_2(X1,X2),X1)
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X4,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v3_yellow_6(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ r1_waybel_0(X2,X1,X3)
    | ~ r2_hidden(X4,k10_yellow_6(X2,X1))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk5_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,esk6_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( v3_yellow_6(esk7_0,esk5_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r1_waybel_0(esk5_0,esk3_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v4_orders_2(esk3_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v7_waybel_0(esk3_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | l1_waybel_0(esk3_2(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ v2_struct_0(esk3_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_36,plain,
    ( r3_waybel_9(X1,esk3_2(X1,X2),esk4_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_37,plain,
    ( v2_struct_0(X3)
    | r2_hidden(X4,X1)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ r1_waybel_0(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_38,plain,
    ( r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X2,esk5_0)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r2_hidden(X1,k10_yellow_6(esk5_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk5_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,esk6_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( v3_yellow_6(esk7_0,esk5_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_48,plain,
    ( v4_orders_2(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_49,plain,
    ( v7_waybel_0(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_50,plain,
    ( l1_waybel_0(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_52,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ r3_waybel_9(esk5_0,esk3_2(esk5_0,esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r3_waybel_9(esk5_0,esk3_2(esk5_0,esk6_0),esk4_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,X1),esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v4_orders_2(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk1_3(esk5_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_61,plain,
    ( r3_waybel_9(X1,esk1_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_22])).

cnf(c_0_65,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk6_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41])).

cnf(c_0_66,negated_conjecture,
    ( v4_orders_2(esk1_3(esk5_0,esk6_0,esk8_0))
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_41])).

cnf(c_0_67,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0))
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_56]),c_0_41])).

cnf(c_0_68,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0),esk5_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_41])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_41])).

cnf(c_0_70,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_72,plain,
    ( v4_orders_2(esk2_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_73,plain,
    ( v7_waybel_0(esk2_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_74,plain,
    ( l1_waybel_0(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_75,plain,
    ( r1_waybel_0(X1,esk2_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_76,plain,
    ( v3_yellow_6(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk2_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_63])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk8_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_56]),c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( v4_orders_2(esk2_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_84,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_85,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_86,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,X1),esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_87,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk2_3(esk5_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_89,plain,
    ( v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_63])).

cnf(c_0_91,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v2_struct_0(X1)
    | r2_hidden(X2,esk6_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v3_yellow_6(X1,esk5_0)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ r1_waybel_0(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_hidden(X2,k10_yellow_6(esk5_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))))
    | r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_40])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_41]),c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))
    | r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_79]),c_0_40])).

cnf(c_0_95,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))
    | r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_79]),c_0_40])).

cnf(c_0_96,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_40])).

cnf(c_0_97,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_79]),c_0_40])).

cnf(c_0_98,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_79]),c_0_40])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))
    | ~ v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_79]),c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(esk4_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))))
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_90]),c_0_41])).

cnf(c_0_102,negated_conjecture,
    ( v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_90]),c_0_41])).

cnf(c_0_103,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_90]),c_0_41])).

cnf(c_0_104,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_90]),c_0_41])).

cnf(c_0_105,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_90]),c_0_41])).

cnf(c_0_106,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)
    | m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_90]),c_0_41])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_90]),c_0_41])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])]),c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_98]),c_0_99]),c_0_100]),c_0_21])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_101]),c_0_93])]),c_0_102]),c_0_103]),c_0_104]),c_0_105]),c_0_106]),c_0_107]),c_0_100]),c_0_23])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))
    | v2_struct_0(esk7_0)
    | ~ v3_yellow_6(esk7_0,esk5_0)
    | ~ r1_waybel_0(esk5_0,esk7_0,esk6_0)
    | ~ l1_waybel_0(esk7_0,esk5_0)
    | ~ v7_waybel_0(esk7_0)
    | ~ v4_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_108]),c_0_109])])).

cnf(c_0_111,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,esk6_0)
    | r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_63])).

cnf(c_0_112,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_63])).

cnf(c_0_113,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_63])).

cnf(c_0_114,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk5_0)
    | r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_63])).

cnf(c_0_115,negated_conjecture,
    ( v3_yellow_6(esk7_0,esk5_0)
    | r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_63])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_63])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_113]),c_0_114]),c_0_115]),c_0_116])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))))
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_117]),c_0_93])])).

cnf(c_0_119,negated_conjecture,
    ( v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_117]),c_0_93])])).

cnf(c_0_120,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_117]),c_0_93])])).

cnf(c_0_121,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_117]),c_0_93])])).

cnf(c_0_122,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_117]),c_0_93])])).

cnf(c_0_123,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_117]),c_0_93])])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))
    | ~ v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_117]),c_0_93])])).

cnf(c_0_125,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_118]),c_0_93])]),c_0_119]),c_0_120]),c_0_121]),c_0_122]),c_0_123]),c_0_124]),c_0_100])).

cnf(c_0_126,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,esk6_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_125])).

cnf(c_0_127,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk5_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( v3_yellow_6(esk7_0,esk5_0)
    | r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_125])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_126]),c_0_127]),c_0_128]),c_0_129]),c_0_130]),c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | r2_hidden(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_134,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_132]),c_0_109])])).

cnf(c_0_135,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_132]),c_0_109])])).

cnf(c_0_136,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_132]),c_0_109])])).

cnf(c_0_137,negated_conjecture,
    ( v4_orders_2(esk1_3(esk5_0,esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_132]),c_0_109])])).

cnf(c_0_138,negated_conjecture,
    ( ~ v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_132]),c_0_109])])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | r2_hidden(X1,esk6_0)
    | ~ r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_135]),c_0_136]),c_0_137])]),c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_132]),c_0_109])])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | ~ r2_hidden(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_109])]),c_0_141])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_142]),c_0_93])])).

cnf(c_0_144,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_142]),c_0_93])])).

cnf(c_0_145,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_142]),c_0_93])])).

cnf(c_0_146,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_142]),c_0_93])])).

cnf(c_0_147,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_142]),c_0_93])])).

cnf(c_0_148,negated_conjecture,
    ( v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_142]),c_0_93])])).

cnf(c_0_149,negated_conjecture,
    ( ~ v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_142]),c_0_93])])).

cnf(c_0_150,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_143]),c_0_144]),c_0_145]),c_0_146]),c_0_147]),c_0_148]),c_0_93])]),c_0_149]),c_0_100])).

cnf(c_0_151,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_150])])).

cnf(c_0_152,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_134]),c_0_135]),c_0_136]),c_0_137])]),c_0_138])).

cnf(c_0_153,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_150])])).

cnf(c_0_154,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_140]),c_0_109])]),c_0_153]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:41 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EA
% 0.19/0.41  # and selection function SelectLComplex.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.041 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t26_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:(((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&v3_yellow_6(X3,X1))&l1_waybel_0(X3,X1))=>(r1_waybel_0(X1,X3,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,k10_yellow_6(X1,X3))=>r2_hidden(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow19)).
% 0.19/0.41  fof(t25_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(r1_waybel_0(X1,X3,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r2_hidden(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow19)).
% 0.19/0.41  fof(t23_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>?[X4]:(((((~(v2_struct_0(X4))&v4_orders_2(X4))&v7_waybel_0(X4))&l1_waybel_0(X4,X1))&r1_waybel_0(X1,X4,X2))&r3_waybel_9(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow19)).
% 0.19/0.41  fof(t24_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>?[X4]:((((((~(v2_struct_0(X4))&v4_orders_2(X4))&v7_waybel_0(X4))&v3_yellow_6(X4,X1))&l1_waybel_0(X4,X1))&r1_waybel_0(X1,X4,X2))&r2_hidden(X3,k10_yellow_6(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow19)).
% 0.19/0.41  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:(((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&v3_yellow_6(X3,X1))&l1_waybel_0(X3,X1))=>(r1_waybel_0(X1,X3,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,k10_yellow_6(X1,X3))=>r2_hidden(X4,X2))))))))), inference(assume_negation,[status(cth)],[t26_yellow19])).
% 0.19/0.41  fof(c_0_5, plain, ![X15, X16, X17, X18]:((~v4_pre_topc(X16,X15)|(v2_struct_0(X17)|~v4_orders_2(X17)|~v7_waybel_0(X17)|~l1_waybel_0(X17,X15)|(~r1_waybel_0(X15,X17,X16)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r3_waybel_9(X15,X17,X18)|r2_hidden(X18,X16)))))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(((((~v2_struct_0(esk3_2(X15,X16))|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(v4_orders_2(esk3_2(X15,X16))|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(v7_waybel_0(esk3_2(X15,X16))|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(l1_waybel_0(esk3_2(X15,X16),X15)|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&((r1_waybel_0(X15,esk3_2(X15,X16),X16)|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((m1_subset_1(esk4_2(X15,X16),u1_struct_0(X15))|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((r3_waybel_9(X15,esk3_2(X15,X16),esk4_2(X15,X16))|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~r2_hidden(esk4_2(X15,X16),X16)|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow19])])])])])])).
% 0.19/0.41  fof(c_0_6, negated_conjecture, ![X25, X26]:(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(((((((~v2_struct_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0))&(v4_orders_2(esk7_0)|~v4_pre_topc(esk6_0,esk5_0)))&(v7_waybel_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0)))&(v3_yellow_6(esk7_0,esk5_0)|~v4_pre_topc(esk6_0,esk5_0)))&(l1_waybel_0(esk7_0,esk5_0)|~v4_pre_topc(esk6_0,esk5_0)))&((r1_waybel_0(esk5_0,esk7_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0))&((m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~v4_pre_topc(esk6_0,esk5_0))&((r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))|~v4_pre_topc(esk6_0,esk5_0))&(~r2_hidden(esk8_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0))))))&(v4_pre_topc(esk6_0,esk5_0)|(v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~v3_yellow_6(X25,esk5_0)|~l1_waybel_0(X25,esk5_0)|(~r1_waybel_0(esk5_0,X25,esk6_0)|(~m1_subset_1(X26,u1_struct_0(esk5_0))|(~r2_hidden(X26,k10_yellow_6(esk5_0,X25))|r2_hidden(X26,esk6_0))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).
% 0.19/0.41  fof(c_0_7, plain, ![X5, X6, X7, X9]:(((((((~v2_struct_0(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(v4_orders_2(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v7_waybel_0(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(l1_waybel_0(esk1_3(X5,X6,X7),X5)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(r1_waybel_0(X5,esk1_3(X5,X6,X7),X6)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(r3_waybel_9(X5,esk1_3(X5,X6,X7),X7)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v2_struct_0(X9)|~v4_orders_2(X9)|~v7_waybel_0(X9)|~l1_waybel_0(X9,X5)|~r1_waybel_0(X5,X9,X6)|~r3_waybel_9(X5,X9,X7)|r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_yellow19])])])])])])).
% 0.19/0.41  fof(c_0_8, plain, ![X10, X11, X12, X14]:((((((((~v2_struct_0(esk2_3(X10,X11,X12))|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(v4_orders_2(esk2_3(X10,X11,X12))|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v7_waybel_0(esk2_3(X10,X11,X12))|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v3_yellow_6(esk2_3(X10,X11,X12),X10)|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(l1_waybel_0(esk2_3(X10,X11,X12),X10)|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(r1_waybel_0(X10,esk2_3(X10,X11,X12),X11)|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(r2_hidden(X12,k10_yellow_6(X10,esk2_3(X10,X11,X12)))|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v2_struct_0(X14)|~v4_orders_2(X14)|~v7_waybel_0(X14)|~v3_yellow_6(X14,X10)|~l1_waybel_0(X14,X10)|~r1_waybel_0(X10,X14,X11)|~r2_hidden(X12,k10_yellow_6(X10,X14))|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_yellow19])])])])])])).
% 0.19/0.41  cnf(c_0_9, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_12, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_14, plain, (v2_struct_0(X1)|r2_hidden(X4,k2_pre_topc(X2,X3))|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~r1_waybel_0(X2,X1,X3)|~r3_waybel_9(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_15, plain, (r1_waybel_0(X1,esk3_2(X1,X2),X2)|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_16, plain, (v4_orders_2(esk3_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_17, plain, (v7_waybel_0(esk3_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_18, plain, (l1_waybel_0(esk3_2(X1,X2),X1)|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_19, plain, (v4_pre_topc(X2,X1)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_20, plain, (v2_struct_0(X1)|r2_hidden(X4,k2_pre_topc(X2,X3))|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~v3_yellow_6(X1,X2)|~l1_waybel_0(X1,X2)|~r1_waybel_0(X2,X1,X3)|~r2_hidden(X4,k10_yellow_6(X2,X1))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (v4_orders_2(esk7_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (v7_waybel_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (l1_waybel_0(esk7_0,esk5_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (v3_yellow_6(esk7_0,esk5_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|v2_struct_0(X2)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r1_waybel_0(esk5_0,esk3_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v4_orders_2(esk3_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v7_waybel_0(esk3_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|l1_waybel_0(esk3_2(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~v2_struct_0(esk3_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_36, plain, (r3_waybel_9(X1,esk3_2(X1,X2),esk4_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_37, plain, (v2_struct_0(X3)|r2_hidden(X4,X1)|v2_struct_0(X2)|~v4_pre_topc(X1,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~r1_waybel_0(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r3_waybel_9(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_38, plain, (r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|v2_struct_0(X2)|~v3_yellow_6(X2,esk5_0)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~r2_hidden(X1,k10_yellow_6(esk5_0,X2))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (v4_orders_2(esk7_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (v7_waybel_0(esk7_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (l1_waybel_0(esk7_0,esk5_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_22])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,esk6_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (v3_yellow_6(esk7_0,esk5_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.19/0.41  cnf(c_0_48, plain, (v4_orders_2(esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_49, plain, (v7_waybel_0(esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_50, plain, (l1_waybel_0(esk1_3(X1,X2,X3),X1)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_51, plain, (v2_struct_0(X1)|~v2_struct_0(esk1_3(X1,X2,X3))|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~r3_waybel_9(esk5_0,esk3_2(esk5_0,esk6_0),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r3_waybel_9(esk5_0,esk3_2(esk5_0,esk6_0),esk4_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(X2)|~v4_pre_topc(esk6_0,esk5_0)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,X1),esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (v4_orders_2(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (v7_waybel_0(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (l1_waybel_0(esk1_3(esk5_0,esk6_0,X1),esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v2_struct_0(esk1_3(esk5_0,esk6_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_61, plain, (r3_waybel_9(X1,esk1_3(X1,X2,X3),X3)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_62, plain, (r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))|v2_struct_0(X2)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_22])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,esk6_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|v2_struct_0(X2)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_54, c_0_22])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk6_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (v4_orders_2(esk1_3(esk5_0,esk6_0,esk8_0))|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_56]), c_0_41])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (v7_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0))|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_56]), c_0_41])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (l1_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0),esk5_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_41])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|~v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_56]), c_0_41])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,X1),X1)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_72, plain, (v4_orders_2(esk2_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_73, plain, (v7_waybel_0(esk2_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_74, plain, (l1_waybel_0(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_75, plain, (r1_waybel_0(X1,esk2_3(X1,X2,X3),X2)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_76, plain, (v3_yellow_6(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_77, plain, (v2_struct_0(X1)|~v2_struct_0(esk2_3(X1,X2,X3))|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,X1)))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))|r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_21, c_0_63])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (r2_hidden(X1,esk6_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|~r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_68]), c_0_69])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk8_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_56]), c_0_41])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|~r2_hidden(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_71, c_0_22])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (v4_orders_2(esk2_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (v7_waybel_0(esk2_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, (l1_waybel_0(esk2_3(esk5_0,esk6_0,X1),esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_86, negated_conjecture, (r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,X1),esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (v3_yellow_6(esk2_3(esk5_0,esk6_0,X1),esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v2_struct_0(esk2_3(esk5_0,esk6_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_89, plain, (v4_pre_topc(X2,X1)|v2_struct_0(X1)|~r2_hidden(esk4_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_63])).
% 0.19/0.41  cnf(c_0_91, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v2_struct_0(X1)|r2_hidden(X2,esk6_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~v3_yellow_6(X1,esk5_0)|~l1_waybel_0(X1,esk5_0)|~r1_waybel_0(esk5_0,X1,esk6_0)|~m1_subset_1(X2,u1_struct_0(esk5_0))|~r2_hidden(X2,k10_yellow_6(esk5_0,X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))))|r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_40])).
% 0.19/0.41  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk4_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_41]), c_0_82])).
% 0.19/0.41  cnf(c_0_94, negated_conjecture, (v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))|r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_79]), c_0_40])).
% 0.19/0.41  cnf(c_0_95, negated_conjecture, (v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))|r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_79]), c_0_40])).
% 0.19/0.41  cnf(c_0_96, negated_conjecture, (l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)|r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_79]), c_0_40])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0)|r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_79]), c_0_40])).
% 0.19/0.41  cnf(c_0_98, negated_conjecture, (v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)|r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_79]), c_0_40])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))|~v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_79]), c_0_40])).
% 0.19/0.41  cnf(c_0_100, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(esk4_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_101, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))))|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_90]), c_0_41])).
% 0.19/0.41  cnf(c_0_102, negated_conjecture, (v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_90]), c_0_41])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_90]), c_0_41])).
% 0.19/0.41  cnf(c_0_104, negated_conjecture, (l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_90]), c_0_41])).
% 0.19/0.41  cnf(c_0_105, negated_conjecture, (r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_90]), c_0_41])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)|m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_90]), c_0_41])).
% 0.19/0.41  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_90]), c_0_41])).
% 0.19/0.41  cnf(c_0_108, negated_conjecture, (r2_hidden(esk8_0,k10_yellow_6(esk5_0,esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])]), c_0_94]), c_0_95]), c_0_96]), c_0_97]), c_0_98]), c_0_99]), c_0_100]), c_0_21])).
% 0.19/0.41  cnf(c_0_109, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_101]), c_0_93])]), c_0_102]), c_0_103]), c_0_104]), c_0_105]), c_0_106]), c_0_107]), c_0_100]), c_0_23])).
% 0.19/0.41  cnf(c_0_110, negated_conjecture, (r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))|v2_struct_0(esk7_0)|~v3_yellow_6(esk7_0,esk5_0)|~r1_waybel_0(esk5_0,esk7_0,esk6_0)|~l1_waybel_0(esk7_0,esk5_0)|~v7_waybel_0(esk7_0)|~v4_orders_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_108]), c_0_109])])).
% 0.19/0.41  cnf(c_0_111, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,esk6_0)|r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_63])).
% 0.19/0.41  cnf(c_0_112, negated_conjecture, (v4_orders_2(esk7_0)|r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_63])).
% 0.19/0.41  cnf(c_0_113, negated_conjecture, (v7_waybel_0(esk7_0)|r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_63])).
% 0.19/0.41  cnf(c_0_114, negated_conjecture, (l1_waybel_0(esk7_0,esk5_0)|r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_63])).
% 0.19/0.41  cnf(c_0_115, negated_conjecture, (v3_yellow_6(esk7_0,esk5_0)|r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_63])).
% 0.19/0.41  cnf(c_0_116, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_63])).
% 0.19/0.41  cnf(c_0_117, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_113]), c_0_114]), c_0_115]), c_0_116])).
% 0.19/0.41  cnf(c_0_118, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))))|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_117]), c_0_93])])).
% 0.19/0.41  cnf(c_0_119, negated_conjecture, (v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_117]), c_0_93])])).
% 0.19/0.41  cnf(c_0_120, negated_conjecture, (v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_117]), c_0_93])])).
% 0.19/0.41  cnf(c_0_121, negated_conjecture, (l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_117]), c_0_93])])).
% 0.19/0.41  cnf(c_0_122, negated_conjecture, (r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_117]), c_0_93])])).
% 0.19/0.41  cnf(c_0_123, negated_conjecture, (v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_117]), c_0_93])])).
% 0.19/0.41  cnf(c_0_124, negated_conjecture, (r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))|~v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_117]), c_0_93])])).
% 0.19/0.41  cnf(c_0_125, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_118]), c_0_93])]), c_0_119]), c_0_120]), c_0_121]), c_0_122]), c_0_123]), c_0_124]), c_0_100])).
% 0.19/0.41  cnf(c_0_126, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,esk6_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_125])).
% 0.19/0.41  cnf(c_0_127, negated_conjecture, (v4_orders_2(esk7_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_125])).
% 0.19/0.41  cnf(c_0_128, negated_conjecture, (v7_waybel_0(esk7_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_125])).
% 0.19/0.41  cnf(c_0_129, negated_conjecture, (l1_waybel_0(esk7_0,esk5_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_125])).
% 0.19/0.41  cnf(c_0_130, negated_conjecture, (v3_yellow_6(esk7_0,esk5_0)|r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_125])).
% 0.19/0.41  cnf(c_0_131, negated_conjecture, (r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_125])).
% 0.19/0.41  cnf(c_0_132, negated_conjecture, (r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_126]), c_0_127]), c_0_128]), c_0_129]), c_0_130]), c_0_131])).
% 0.19/0.41  cnf(c_0_133, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))|r2_hidden(X1,esk6_0)|v2_struct_0(X2)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_54, c_0_63])).
% 0.19/0.41  cnf(c_0_134, negated_conjecture, (r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_132]), c_0_109])])).
% 0.19/0.41  cnf(c_0_135, negated_conjecture, (l1_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_132]), c_0_109])])).
% 0.19/0.41  cnf(c_0_136, negated_conjecture, (v7_waybel_0(esk1_3(esk5_0,esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_132]), c_0_109])])).
% 0.19/0.41  cnf(c_0_137, negated_conjecture, (v4_orders_2(esk1_3(esk5_0,esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_132]), c_0_109])])).
% 0.19/0.41  cnf(c_0_138, negated_conjecture, (~v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_132]), c_0_109])])).
% 0.19/0.41  cnf(c_0_139, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))|r2_hidden(X1,esk6_0)|~r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_135]), c_0_136]), c_0_137])]), c_0_138])).
% 0.19/0.41  cnf(c_0_140, negated_conjecture, (r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_132]), c_0_109])])).
% 0.19/0.41  cnf(c_0_141, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))|~r2_hidden(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_71, c_0_63])).
% 0.19/0.41  cnf(c_0_142, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_109])]), c_0_141])).
% 0.19/0.41  cnf(c_0_143, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_142]), c_0_93])])).
% 0.19/0.41  cnf(c_0_144, negated_conjecture, (v3_yellow_6(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_142]), c_0_93])])).
% 0.19/0.41  cnf(c_0_145, negated_conjecture, (r1_waybel_0(esk5_0,esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_142]), c_0_93])])).
% 0.19/0.41  cnf(c_0_146, negated_conjecture, (l1_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_142]), c_0_93])])).
% 0.19/0.41  cnf(c_0_147, negated_conjecture, (v7_waybel_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_142]), c_0_93])])).
% 0.19/0.41  cnf(c_0_148, negated_conjecture, (v4_orders_2(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_142]), c_0_93])])).
% 0.19/0.41  cnf(c_0_149, negated_conjecture, (~v2_struct_0(esk2_3(esk5_0,esk6_0,esk4_2(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_142]), c_0_93])])).
% 0.19/0.41  cnf(c_0_150, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_143]), c_0_144]), c_0_145]), c_0_146]), c_0_147]), c_0_148]), c_0_93])]), c_0_149]), c_0_100])).
% 0.19/0.41  cnf(c_0_151, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(X2)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_150])])).
% 0.19/0.41  cnf(c_0_152, negated_conjecture, (r2_hidden(X1,esk6_0)|~r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,esk8_0),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_134]), c_0_135]), c_0_136]), c_0_137])]), c_0_138])).
% 0.19/0.41  cnf(c_0_153, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_150])])).
% 0.19/0.41  cnf(c_0_154, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_140]), c_0_109])]), c_0_153]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 155
% 0.19/0.41  # Proof object clause steps            : 146
% 0.19/0.41  # Proof object formula steps           : 9
% 0.19/0.41  # Proof object conjectures             : 125
% 0.19/0.41  # Proof object clause conjectures      : 122
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 38
% 0.19/0.41  # Proof object initial formulas used   : 4
% 0.19/0.41  # Proof object generating inferences   : 106
% 0.19/0.41  # Proof object simplifying inferences  : 244
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 4
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 38
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 38
% 0.19/0.41  # Processed clauses                    : 278
% 0.19/0.41  # ...of these trivial                  : 5
% 0.19/0.41  # ...subsumed                          : 19
% 0.19/0.41  # ...remaining for further processing  : 254
% 0.19/0.41  # Other redundant clauses eliminated   : 0
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 6
% 0.19/0.41  # Backward-rewritten                   : 115
% 0.19/0.41  # Generated clauses                    : 226
% 0.19/0.41  # ...of the previous two non-trivial   : 229
% 0.19/0.41  # Contextual simplify-reflections      : 140
% 0.19/0.41  # Paramodulations                      : 221
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 0
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 90
% 0.19/0.41  #    Positive orientable unit clauses  : 36
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 7
% 0.19/0.41  #    Non-unit-clauses                  : 47
% 0.19/0.41  # Current number of unprocessed clauses: 10
% 0.19/0.41  # ...number of literals in the above   : 46
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 164
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 4352
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1363
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 163
% 0.19/0.41  # Unit Clause-clause subsumption calls : 342
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 37
% 0.19/0.41  # BW rewrite match successes           : 6
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 11833
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.060 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.065 s
% 0.19/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
