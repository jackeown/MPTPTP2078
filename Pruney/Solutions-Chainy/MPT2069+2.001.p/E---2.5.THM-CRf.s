%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 (5569 expanded)
%              Number of clauses        :   79 (1725 expanded)
%              Number of leaves         :    4 (1371 expanded)
%              Depth                    :   14
%              Number of atoms          :  621 (89963 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   62 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                  & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                  & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
               => ( r2_hidden(X2,X3)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_waybel_7(X1,X3,X4)
                       => r2_hidden(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow19)).

fof(t27_yellow19,axiom,(
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
                    ( ~ v1_xboole_0(X4)
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
                    & r2_hidden(X2,X4)
                    & r1_waybel_7(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow19)).

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

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> ! [X3] :
                  ( ( ~ v1_xboole_0(X3)
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
                 => ( r2_hidden(X2,X3)
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r1_waybel_7(X1,X3,X4)
                         => r2_hidden(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow19])).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X20] :
      ( ( ~ v1_xboole_0(esk4_3(X16,X17,X18))
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v1_subset_1(esk4_3(X16,X17,X18),u1_struct_0(k3_yellow_1(k2_struct_0(X16))))
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v2_waybel_0(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v13_waybel_0(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk4_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X16)))))
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(X17,esk4_3(X16,X17,X18))
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r1_waybel_7(X16,esk4_3(X16,X17,X18),X18)
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v1_xboole_0(X20)
        | ~ v1_subset_1(X20,u1_struct_0(k3_yellow_1(k2_struct_0(X16))))
        | ~ v2_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))
        | ~ v13_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X16)))))
        | ~ r2_hidden(X17,X20)
        | ~ r1_waybel_7(X16,X20,X18)
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow19])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X25,X26] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & ( ~ v1_xboole_0(esk7_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( r2_hidden(esk6_0,esk7_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( r1_waybel_7(esk5_0,esk7_0,esk8_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( ~ r2_hidden(esk8_0,esk6_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v4_pre_topc(esk6_0,esk5_0)
        | v1_xboole_0(X25)
        | ~ v1_subset_1(X25,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
        | ~ v2_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v13_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
        | ~ r2_hidden(esk6_0,X25)
        | ~ m1_subset_1(X26,u1_struct_0(esk5_0))
        | ~ r1_waybel_7(esk5_0,X25,X26)
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
    ! [X10,X11,X12,X13] :
      ( ( ~ v4_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X10)
        | ~ r1_waybel_0(X10,X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r3_waybel_9(X10,X12,X13)
        | r2_hidden(X13,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v2_struct_0(esk2_2(X10,X11))
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v4_orders_2(esk2_2(X10,X11))
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v7_waybel_0(esk2_2(X10,X11))
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( l1_waybel_0(esk2_2(X10,X11),X10)
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r1_waybel_0(X10,esk2_2(X10,X11),X11)
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk3_2(X10,X11),u1_struct_0(X10))
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r3_waybel_9(X10,esk2_2(X10,X11),esk3_2(X10,X11))
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(esk3_2(X10,X11),X11)
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow19])])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
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
    ( r2_hidden(X1,esk4_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( v1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( v2_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( v13_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
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

cnf(c_0_19,plain,
    ( r1_waybel_0(X1,esk2_2(X1,X2),X2)
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( v4_orders_2(esk2_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( v7_waybel_0(esk2_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( l1_waybel_0(esk2_2(X1,X2),X1)
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v1_xboole_0(X1)
    | r2_hidden(X2,esk6_0)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r1_waybel_7(esk5_0,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v1_subset_1(esk4_3(esk5_0,esk6_0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v2_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( v13_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_30,plain,
    ( r1_waybel_7(X1,esk4_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r1_waybel_0(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v4_orders_2(esk2_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v7_waybel_0(esk2_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | l1_waybel_0(esk2_2(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ v2_struct_0(esk2_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_37,plain,
    ( r3_waybel_9(X1,esk2_2(X1,X2),esk3_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))
    | v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(X2,esk6_0)
    | ~ r1_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X2)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r1_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ r3_waybel_9(esk5_0,esk2_2(esk5_0,esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r3_waybel_9(esk5_0,esk2_2(esk5_0,esk6_0),esk3_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_44,plain,
    ( v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))
    | v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(esk3_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(esk3_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk4_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk4_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_43]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_10]),c_0_11]),c_0_12])]),c_0_13]),c_0_43]),c_0_46])).

cnf(c_0_53,plain,
    ( r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_54,plain,
    ( v4_orders_2(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_55,plain,
    ( v7_waybel_0(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_56,plain,
    ( l1_waybel_0(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk5_0,X2,X1)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_58,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,X1),esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( v4_orders_2(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_62,plain,
    ( r3_waybel_9(X1,esk1_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(X4,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X2))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))
    | ~ r2_hidden(X3,X1)
    | ~ r1_waybel_7(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_65,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_66,negated_conjecture,
    ( v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_67,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(esk1_3(esk5_0,esk6_0,X2))
    | ~ r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,X2))
    | ~ r1_waybel_7(esk5_0,esk7_0,X1)
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_11]),c_0_12])]),c_0_13]),c_0_65]),c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,X2))
    | ~ r1_waybel_7(esk5_0,esk7_0,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_52])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_52])])).

cnf(c_0_77,negated_conjecture,
    ( r1_waybel_7(esk5_0,esk7_0,esk8_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_waybel_7(esk5_0,esk7_0,X1)
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk1_3(esk5_0,X2,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_71]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(esk1_3(esk5_0,esk6_0,X1))
    | ~ r1_waybel_7(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_10])])).

cnf(c_0_82,negated_conjecture,
    ( r1_waybel_7(esk5_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_52])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_52])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_52])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_waybel_7(esk5_0,esk7_0,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk1_3(esk5_0,X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_52])])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_82]),c_0_76]),c_0_10]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:48:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.029 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t29_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:(((((~(v1_xboole_0(X3))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_hidden(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_waybel_7(X1,X3,X4)=>r2_hidden(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow19)).
% 0.19/0.39  fof(t27_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>?[X4]:((((((~(v1_xboole_0(X4))&v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))&r2_hidden(X2,X4))&r1_waybel_7(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow19)).
% 0.19/0.39  fof(t23_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>?[X4]:(((((~(v2_struct_0(X4))&v4_orders_2(X4))&v7_waybel_0(X4))&l1_waybel_0(X4,X1))&r1_waybel_0(X1,X4,X2))&r3_waybel_9(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow19)).
% 0.19/0.39  fof(t25_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(r1_waybel_0(X1,X3,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r2_hidden(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow19)).
% 0.19/0.39  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:(((((~(v1_xboole_0(X3))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_hidden(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_waybel_7(X1,X3,X4)=>r2_hidden(X4,X2))))))))), inference(assume_negation,[status(cth)],[t29_yellow19])).
% 0.19/0.39  fof(c_0_5, plain, ![X16, X17, X18, X20]:((((((((~v1_xboole_0(esk4_3(X16,X17,X18))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(v1_subset_1(esk4_3(X16,X17,X18),u1_struct_0(k3_yellow_1(k2_struct_0(X16))))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(v2_waybel_0(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(v13_waybel_0(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(m1_subset_1(esk4_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X16)))))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(r2_hidden(X17,esk4_3(X16,X17,X18))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(r1_waybel_7(X16,esk4_3(X16,X17,X18),X18)|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(v1_xboole_0(X20)|~v1_subset_1(X20,u1_struct_0(k3_yellow_1(k2_struct_0(X16))))|~v2_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))|~v13_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X16)))))|~r2_hidden(X17,X20)|~r1_waybel_7(X16,X20,X18)|r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow19])])])])])])).
% 0.19/0.39  fof(c_0_6, negated_conjecture, ![X25, X26]:(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(((((((~v1_xboole_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0))&(v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))|~v4_pre_topc(esk6_0,esk5_0)))&(v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)))&(v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~v4_pre_topc(esk6_0,esk5_0)))&((r2_hidden(esk6_0,esk7_0)|~v4_pre_topc(esk6_0,esk5_0))&((m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~v4_pre_topc(esk6_0,esk5_0))&((r1_waybel_7(esk5_0,esk7_0,esk8_0)|~v4_pre_topc(esk6_0,esk5_0))&(~r2_hidden(esk8_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0))))))&(v4_pre_topc(esk6_0,esk5_0)|(v1_xboole_0(X25)|~v1_subset_1(X25,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))|~v2_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))|~v13_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|(~r2_hidden(esk6_0,X25)|(~m1_subset_1(X26,u1_struct_0(esk5_0))|(~r1_waybel_7(esk5_0,X25,X26)|r2_hidden(X26,esk6_0))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).
% 0.19/0.39  fof(c_0_7, plain, ![X5, X6, X7, X9]:(((((((~v2_struct_0(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(v4_orders_2(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v7_waybel_0(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(l1_waybel_0(esk1_3(X5,X6,X7),X5)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(r1_waybel_0(X5,esk1_3(X5,X6,X7),X6)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(r3_waybel_9(X5,esk1_3(X5,X6,X7),X7)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v2_struct_0(X9)|~v4_orders_2(X9)|~v7_waybel_0(X9)|~l1_waybel_0(X9,X5)|~r1_waybel_0(X5,X9,X6)|~r3_waybel_9(X5,X9,X7)|r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_yellow19])])])])])])).
% 0.19/0.39  fof(c_0_8, plain, ![X10, X11, X12, X13]:((~v4_pre_topc(X11,X10)|(v2_struct_0(X12)|~v4_orders_2(X12)|~v7_waybel_0(X12)|~l1_waybel_0(X12,X10)|(~r1_waybel_0(X10,X12,X11)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r3_waybel_9(X10,X12,X13)|r2_hidden(X13,X11)))))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(((((~v2_struct_0(esk2_2(X10,X11))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(v4_orders_2(esk2_2(X10,X11))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v7_waybel_0(esk2_2(X10,X11))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(l1_waybel_0(esk2_2(X10,X11),X10)|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&((r1_waybel_0(X10,esk2_2(X10,X11),X11)|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((m1_subset_1(esk3_2(X10,X11),u1_struct_0(X10))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((r3_waybel_9(X10,esk2_2(X10,X11),esk3_2(X10,X11))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~r2_hidden(esk3_2(X10,X11),X11)|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow19])])])])])])).
% 0.19/0.39  cnf(c_0_9, plain, (m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_12, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_14, plain, (r2_hidden(X1,esk4_3(X2,X1,X3))|v2_struct_0(X2)|~r2_hidden(X3,k2_pre_topc(X2,X1))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_15, plain, (v1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_16, plain, (v2_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_17, plain, (v13_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_18, plain, (v2_struct_0(X1)|r2_hidden(X4,k2_pre_topc(X2,X3))|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~r1_waybel_0(X2,X1,X3)|~r3_waybel_9(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_19, plain, (r1_waybel_0(X1,esk2_2(X1,X2),X2)|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_20, plain, (v4_orders_2(esk2_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_21, plain, (v7_waybel_0(esk2_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_22, plain, (l1_waybel_0(esk2_2(X1,X2),X1)|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_23, plain, (v4_pre_topc(X2,X1)|v2_struct_0(X1)|~v2_struct_0(esk2_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v1_xboole_0(X1)|r2_hidden(X2,esk6_0)|~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))|~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))|~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~r2_hidden(esk6_0,X1)|~m1_subset_1(X2,u1_struct_0(esk5_0))|~r1_waybel_7(esk5_0,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,esk4_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (v1_subset_1(esk4_3(esk5_0,esk6_0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (v2_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (v13_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_30, plain, (r1_waybel_7(X1,esk4_3(X1,X2,X3),X3)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|v2_struct_0(X2)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r1_waybel_0(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v4_orders_2(esk2_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v7_waybel_0(esk2_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|l1_waybel_0(esk2_2(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~v2_struct_0(esk2_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_37, plain, (r3_waybel_9(X1,esk2_2(X1,X2),esk3_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_38, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))|v4_pre_topc(esk6_0,esk5_0)|r2_hidden(X2,esk6_0)|~r1_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X2)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (r1_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X1)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~r3_waybel_9(esk5_0,esk2_2(esk5_0,esk6_0),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r3_waybel_9(esk5_0,esk2_2(esk5_0,esk6_0),esk3_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_44, plain, (v4_pre_topc(X2,X1)|v2_struct_0(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))|v4_pre_topc(esk6_0,esk5_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(esk3_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(esk3_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_48, plain, (v2_struct_0(X3)|r2_hidden(X4,X1)|v2_struct_0(X2)|~v4_pre_topc(X1,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~r1_waybel_0(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r3_waybel_9(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_49, plain, (v2_struct_0(X1)|~v1_xboole_0(esk4_3(X1,X2,X3))|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk4_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))|v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_43]), c_0_47])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(X2)|~v4_pre_topc(esk6_0,esk5_0)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_10]), c_0_11]), c_0_12])]), c_0_13]), c_0_43]), c_0_46])).
% 0.19/0.39  cnf(c_0_53, plain, (r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_54, plain, (v4_orders_2(esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_55, plain, (v7_waybel_0(esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_56, plain, (l1_waybel_0(esk1_3(X1,X2,X3),X1)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(X2)|~r3_waybel_9(esk5_0,X2,X1)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,X1),esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (v4_orders_2(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (v7_waybel_0(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (l1_waybel_0(esk1_3(esk5_0,esk6_0,X1),esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_62, plain, (r3_waybel_9(X1,esk1_3(X1,X2,X3),X3)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_63, plain, (v1_xboole_0(X1)|r2_hidden(X4,k2_pre_topc(X2,X3))|v2_struct_0(X2)|~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X2))))|~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))|~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))|~r2_hidden(X3,X1)|~r1_waybel_7(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(esk1_3(esk5_0,esk6_0,X2))|~r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,X2),X1)|~r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_61])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, (r3_waybel_9(esk5_0,esk1_3(esk5_0,esk6_0,X1),X1)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,X2))|~r1_waybel_7(esk5_0,esk7_0,X1)|~v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(X2,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_11]), c_0_12])]), c_0_13]), c_0_65]), c_0_66]), c_0_67]), c_0_68])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_73, plain, (v2_struct_0(X1)|~v2_struct_0(esk1_3(X1,X2,X3))|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,X2))|~r1_waybel_7(esk5_0,esk7_0,X1)|~r2_hidden(X2,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_52])])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_52])])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (r1_waybel_7(esk5_0,esk7_0,esk8_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (~r1_waybel_7(esk5_0,esk7_0,X1)|~v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(X2,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v2_struct_0(esk1_3(esk5_0,X2,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_71]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(esk1_3(esk5_0,esk6_0,X1))|~r1_waybel_7(esk5_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_10])])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (r1_waybel_7(esk5_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_52])])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_52])])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_52])])).
% 0.19/0.39  cnf(c_0_85, negated_conjecture, (~r1_waybel_7(esk5_0,esk7_0,X1)|~r2_hidden(X2,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v2_struct_0(esk1_3(esk5_0,X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_52])])).
% 0.19/0.39  cnf(c_0_86, negated_conjecture, (v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])]), c_0_84])).
% 0.19/0.39  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_82]), c_0_76]), c_0_10]), c_0_83])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 88
% 0.19/0.39  # Proof object clause steps            : 79
% 0.19/0.39  # Proof object formula steps           : 9
% 0.19/0.39  # Proof object conjectures             : 58
% 0.19/0.39  # Proof object clause conjectures      : 55
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 38
% 0.19/0.39  # Proof object initial formulas used   : 4
% 0.19/0.39  # Proof object generating inferences   : 34
% 0.19/0.39  # Proof object simplifying inferences  : 142
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 4
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 38
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 38
% 0.19/0.39  # Processed clauses                    : 200
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 18
% 0.19/0.39  # ...remaining for further processing  : 182
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 47
% 0.19/0.39  # Generated clauses                    : 105
% 0.19/0.39  # ...of the previous two non-trivial   : 133
% 0.19/0.39  # Contextual simplify-reflections      : 24
% 0.19/0.39  # Paramodulations                      : 105
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 97
% 0.19/0.39  #    Positive orientable unit clauses  : 12
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 82
% 0.19/0.39  # Current number of unprocessed clauses: 9
% 0.19/0.39  # ...number of literals in the above   : 91
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 85
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 9340
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 470
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 42
% 0.19/0.39  # Unit Clause-clause subsumption calls : 494
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 4
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 11967
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.046 s
% 0.19/0.40  # System time              : 0.009 s
% 0.19/0.40  # Total time               : 0.055 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
