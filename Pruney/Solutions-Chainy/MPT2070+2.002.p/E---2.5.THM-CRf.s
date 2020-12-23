%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:05 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   89 (7122 expanded)
%              Number of clauses        :   80 (2185 expanded)
%              Number of leaves         :    4 (1761 expanded)
%              Depth                    :   13
%              Number of atoms          :  640 (117550 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                  & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                  & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X1)))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
               => ( r2_hidden(X2,X3)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_waybel_7(X1,X3,X4)
                       => r2_hidden(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow19)).

fof(t28_yellow19,axiom,(
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
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X1)))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
                    & r2_hidden(X2,X4)
                    & r2_waybel_7(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow19)).

fof(t26_yellow19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow19)).

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
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X1)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
                 => ( r2_hidden(X2,X3)
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r2_waybel_7(X1,X3,X4)
                         => r2_hidden(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_yellow19])).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X20] :
      ( ( ~ v1_xboole_0(esk4_3(X16,X17,X18))
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
      & ( v3_waybel_7(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))
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
      & ( r2_waybel_7(X16,esk4_3(X16,X17,X18),X18)
        | ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))
        | ~ v13_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))
        | ~ v3_waybel_7(X20,k3_yellow_1(k2_struct_0(X16)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X16)))))
        | ~ r2_hidden(X17,X20)
        | ~ r2_waybel_7(X16,X20,X18)
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_yellow19])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X25,X26] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & ( ~ v1_xboole_0(esk7_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v3_waybel_7(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( r2_hidden(esk6_0,esk7_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( r2_waybel_7(esk5_0,esk7_0,esk8_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( ~ r2_hidden(esk8_0,esk6_0)
        | ~ v4_pre_topc(esk6_0,esk5_0) )
      & ( v4_pre_topc(esk6_0,esk5_0)
        | v1_xboole_0(X25)
        | ~ v2_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v13_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v3_waybel_7(X25,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
        | ~ r2_hidden(esk6_0,X25)
        | ~ m1_subset_1(X26,u1_struct_0(esk5_0))
        | ~ r2_waybel_7(esk5_0,X25,X26)
        | r2_hidden(X26,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,esk4_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( v2_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( v13_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( v3_waybel_7(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
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
      & ( v3_yellow_6(esk1_3(X5,X6,X7),X5)
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
      & ( r2_hidden(X7,k10_yellow_6(X5,esk1_3(X5,X6,X7)))
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ v3_yellow_6(X9,X5)
        | ~ l1_waybel_0(X9,X5)
        | ~ r1_waybel_0(X5,X9,X6)
        | ~ r2_hidden(X7,k10_yellow_6(X5,X9))
        | r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_yellow19])])])])])])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ v4_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ v3_yellow_6(X12,X10)
        | ~ l1_waybel_0(X12,X10)
        | ~ r1_waybel_0(X10,X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,k10_yellow_6(X10,X12))
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
      & ( v3_yellow_6(esk2_2(X10,X11),X10)
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
      & ( r2_hidden(esk3_2(X10,X11),k10_yellow_6(X10,esk2_2(X10,X11)))
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow19])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v1_xboole_0(X1)
    | r2_hidden(X2,esk6_0)
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v3_waybel_7(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_waybel_7(esk5_0,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v2_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v13_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( v3_waybel_7(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_24,plain,
    ( r2_waybel_7(X1,esk4_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(esk3_2(X1,X2),k10_yellow_6(X1,esk2_2(X1,X2)))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( v4_orders_2(esk2_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( v7_waybel_0(esk2_2(X1,X2))
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( v3_yellow_6(esk2_2(X1,X2),X1)
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( l1_waybel_0(esk2_2(X1,X2),X1)
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( r1_waybel_0(X1,esk2_2(X1,X2),X2)
    | v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))
    | v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(X2,esk6_0)
    | ~ r2_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X2)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | v2_struct_0(X2)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v3_yellow_6(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r2_hidden(X1,k10_yellow_6(esk5_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v4_orders_2(esk2_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v7_waybel_0(esk2_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v3_yellow_6(esk2_2(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | l1_waybel_0(esk2_2(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r1_waybel_0(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ v2_struct_0(esk2_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_45,plain,
    ( v4_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))
    | v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(esk3_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(esk3_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(X4,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))
    | ~ v3_waybel_7(X1,k3_yellow_1(k2_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))
    | ~ r2_hidden(X3,X1)
    | ~ r2_waybel_7(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_51,negated_conjecture,
    ( v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_52,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_53,negated_conjecture,
    ( v3_waybel_7(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk4_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk4_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38]),c_0_48])).

cnf(c_0_57,plain,
    ( v2_struct_0(X3)
    | r2_hidden(X4,X1)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ v3_yellow_6(X3,X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ r1_waybel_0(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X4,k10_yellow_6(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,X2))
    | ~ r2_waybel_7(esk5_0,esk7_0,X1)
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_9]),c_0_10])]),c_0_11]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_8]),c_0_9]),c_0_10])]),c_0_11]),c_0_38]),c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v3_yellow_6(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r2_hidden(X1,k10_yellow_6(esk5_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk1_3(X2,X3,X1)))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,plain,
    ( v4_orders_2(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_64,plain,
    ( v7_waybel_0(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,plain,
    ( v3_yellow_6(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,plain,
    ( l1_waybel_0(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,plain,
    ( r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,X2))
    | ~ r2_waybel_7(esk5_0,esk7_0,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk8_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ r1_waybel_0(esk5_0,X2,esk6_0)
    | ~ l1_waybel_0(X2,esk5_0)
    | ~ v3_yellow_6(X2,esk5_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r2_hidden(X1,k10_yellow_6(esk5_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_59])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk5_0,esk1_3(esk5_0,esk6_0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_74,negated_conjecture,
    ( v4_orders_2(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_75,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_76,negated_conjecture,
    ( v3_yellow_6(esk1_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_77,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk5_0,esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_78,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,X1),esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ r2_waybel_7(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_8]),c_0_69])])).

cnf(c_0_80,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_59])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_59])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0)
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v2_struct_0(esk1_3(esk5_0,esk6_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_59])])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_87,negated_conjecture,
    ( v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_81])]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_84]),c_0_8]),c_0_81]),c_0_9]),c_0_10])]),c_0_11]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:25:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t30_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:(((((~(v1_xboole_0(X3))&v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_hidden(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_waybel_7(X1,X3,X4)=>r2_hidden(X4,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow19)).
% 0.13/0.39  fof(t28_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>?[X4]:((((((~(v1_xboole_0(X4))&v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))))&v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))&r2_hidden(X2,X4))&r2_waybel_7(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_yellow19)).
% 0.13/0.39  fof(t24_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>?[X4]:((((((~(v2_struct_0(X4))&v4_orders_2(X4))&v7_waybel_0(X4))&v3_yellow_6(X4,X1))&l1_waybel_0(X4,X1))&r1_waybel_0(X1,X4,X2))&r2_hidden(X3,k10_yellow_6(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow19)).
% 0.13/0.39  fof(t26_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:(((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&v3_yellow_6(X3,X1))&l1_waybel_0(X3,X1))=>(r1_waybel_0(X1,X3,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,k10_yellow_6(X1,X3))=>r2_hidden(X4,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow19)).
% 0.13/0.39  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>![X3]:(((((~(v1_xboole_0(X3))&v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))))&v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_hidden(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_waybel_7(X1,X3,X4)=>r2_hidden(X4,X2))))))))), inference(assume_negation,[status(cth)],[t30_yellow19])).
% 0.13/0.39  fof(c_0_5, plain, ![X16, X17, X18, X20]:((((((((~v1_xboole_0(esk4_3(X16,X17,X18))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(v2_waybel_0(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(v13_waybel_0(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(v3_waybel_7(esk4_3(X16,X17,X18),k3_yellow_1(k2_struct_0(X16)))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(m1_subset_1(esk4_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X16)))))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(r2_hidden(X17,esk4_3(X16,X17,X18))|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(r2_waybel_7(X16,esk4_3(X16,X17,X18),X18)|~r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&(v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))|~v13_waybel_0(X20,k3_yellow_1(k2_struct_0(X16)))|~v3_waybel_7(X20,k3_yellow_1(k2_struct_0(X16)))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X16)))))|~r2_hidden(X17,X20)|~r2_waybel_7(X16,X20,X18)|r2_hidden(X18,k2_pre_topc(X16,X17))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_yellow19])])])])])])).
% 0.13/0.39  fof(c_0_6, negated_conjecture, ![X25, X26]:(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(((((((~v1_xboole_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0))&(v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)))&(v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)))&(v3_waybel_7(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~v4_pre_topc(esk6_0,esk5_0)))&((r2_hidden(esk6_0,esk7_0)|~v4_pre_topc(esk6_0,esk5_0))&((m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~v4_pre_topc(esk6_0,esk5_0))&((r2_waybel_7(esk5_0,esk7_0,esk8_0)|~v4_pre_topc(esk6_0,esk5_0))&(~r2_hidden(esk8_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0))))))&(v4_pre_topc(esk6_0,esk5_0)|(v1_xboole_0(X25)|~v2_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))|~v13_waybel_0(X25,k3_yellow_1(k2_struct_0(esk5_0)))|~v3_waybel_7(X25,k3_yellow_1(k2_struct_0(esk5_0)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|(~r2_hidden(esk6_0,X25)|(~m1_subset_1(X26,u1_struct_0(esk5_0))|(~r2_waybel_7(esk5_0,X25,X26)|r2_hidden(X26,esk6_0))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).
% 0.13/0.39  cnf(c_0_7, plain, (m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_9, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_10, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_11, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_12, plain, (r2_hidden(X1,esk4_3(X2,X1,X3))|v2_struct_0(X2)|~r2_hidden(X3,k2_pre_topc(X2,X1))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_13, plain, (v2_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_14, plain, (v13_waybel_0(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_15, plain, (v3_waybel_7(esk4_3(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  fof(c_0_16, plain, ![X5, X6, X7, X9]:((((((((~v2_struct_0(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(v4_orders_2(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v7_waybel_0(esk1_3(X5,X6,X7))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v3_yellow_6(esk1_3(X5,X6,X7),X5)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(l1_waybel_0(esk1_3(X5,X6,X7),X5)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(r1_waybel_0(X5,esk1_3(X5,X6,X7),X6)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(r2_hidden(X7,k10_yellow_6(X5,esk1_3(X5,X6,X7)))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v2_struct_0(X9)|~v4_orders_2(X9)|~v7_waybel_0(X9)|~v3_yellow_6(X9,X5)|~l1_waybel_0(X9,X5)|~r1_waybel_0(X5,X9,X6)|~r2_hidden(X7,k10_yellow_6(X5,X9))|r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_yellow19])])])])])])).
% 0.13/0.39  fof(c_0_17, plain, ![X10, X11, X12, X13]:((~v4_pre_topc(X11,X10)|(v2_struct_0(X12)|~v4_orders_2(X12)|~v7_waybel_0(X12)|~v3_yellow_6(X12,X10)|~l1_waybel_0(X12,X10)|(~r1_waybel_0(X10,X12,X11)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,k10_yellow_6(X10,X12))|r2_hidden(X13,X11)))))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((((((~v2_struct_0(esk2_2(X10,X11))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(v4_orders_2(esk2_2(X10,X11))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v7_waybel_0(esk2_2(X10,X11))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v3_yellow_6(esk2_2(X10,X11),X10)|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(l1_waybel_0(esk2_2(X10,X11),X10)|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&((r1_waybel_0(X10,esk2_2(X10,X11),X11)|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((m1_subset_1(esk3_2(X10,X11),u1_struct_0(X10))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((r2_hidden(esk3_2(X10,X11),k10_yellow_6(X10,esk2_2(X10,X11)))|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~r2_hidden(esk3_2(X10,X11),X11)|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow19])])])])])])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v1_xboole_0(X1)|r2_hidden(X2,esk6_0)|~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))|~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))|~v3_waybel_7(X1,k3_yellow_1(k2_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~r2_hidden(esk6_0,X1)|~m1_subset_1(X2,u1_struct_0(esk5_0))|~r2_waybel_7(esk5_0,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(esk6_0,esk4_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (v2_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (v13_waybel_0(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (v3_waybel_7(esk4_3(esk5_0,esk6_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_24, plain, (r2_waybel_7(X1,esk4_3(X1,X2,X3),X3)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_25, plain, (v2_struct_0(X1)|r2_hidden(X4,k2_pre_topc(X2,X3))|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~v3_yellow_6(X1,X2)|~l1_waybel_0(X1,X2)|~r1_waybel_0(X2,X1,X3)|~r2_hidden(X4,k10_yellow_6(X2,X1))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_26, plain, (r2_hidden(esk3_2(X1,X2),k10_yellow_6(X1,esk2_2(X1,X2)))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_27, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_28, plain, (v4_orders_2(esk2_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_29, plain, (v7_waybel_0(esk2_2(X1,X2))|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_30, plain, (v3_yellow_6(esk2_2(X1,X2),X1)|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_31, plain, (l1_waybel_0(esk2_2(X1,X2),X1)|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_32, plain, (r1_waybel_0(X1,esk2_2(X1,X2),X2)|v4_pre_topc(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_33, plain, (v4_pre_topc(X2,X1)|v2_struct_0(X1)|~v2_struct_0(esk2_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))|v4_pre_topc(esk6_0,esk5_0)|r2_hidden(X2,esk6_0)|~r2_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X2)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r2_waybel_7(esk5_0,esk4_3(esk5_0,esk6_0,X1),X1)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|v2_struct_0(X2)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v3_yellow_6(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~r2_hidden(X1,k10_yellow_6(esk5_0,X2))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_2(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v4_orders_2(esk2_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v7_waybel_0(esk2_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v3_yellow_6(esk2_2(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|l1_waybel_0(esk2_2(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r1_waybel_0(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~v2_struct_0(esk2_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_45, plain, (v4_pre_topc(X2,X1)|v2_struct_0(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (v1_xboole_0(esk4_3(esk5_0,esk6_0,X1))|v4_pre_topc(esk6_0,esk5_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(esk3_2(esk5_0,esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(esk3_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_49, plain, (v1_xboole_0(X1)|r2_hidden(X4,k2_pre_topc(X2,X3))|v2_struct_0(X2)|~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))|~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X2)))|~v3_waybel_7(X1,k3_yellow_1(k2_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))|~r2_hidden(X3,X1)|~r2_waybel_7(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (v2_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (v3_waybel_7(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (~v1_xboole_0(esk7_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_55, plain, (v2_struct_0(X1)|~v1_xboole_0(esk4_3(X1,X2,X3))|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (v1_xboole_0(esk4_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))|v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_38]), c_0_48])).
% 0.13/0.39  cnf(c_0_57, plain, (v2_struct_0(X3)|r2_hidden(X4,X1)|v2_struct_0(X2)|~v4_pre_topc(X1,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~v3_yellow_6(X3,X2)|~l1_waybel_0(X3,X2)|~r1_waybel_0(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X4,k10_yellow_6(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,X2))|~r2_waybel_7(esk5_0,esk7_0,X1)|~v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(X2,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_9]), c_0_10])]), c_0_11]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_8]), c_0_9]), c_0_10])]), c_0_11]), c_0_38]), c_0_47])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(X2)|~v4_pre_topc(esk6_0,esk5_0)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v3_yellow_6(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~r2_hidden(X1,k10_yellow_6(esk5_0,X2))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_62, plain, (r2_hidden(X1,k10_yellow_6(X2,esk1_3(X2,X3,X1)))|v2_struct_0(X2)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_63, plain, (v4_orders_2(esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_64, plain, (v7_waybel_0(esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_65, plain, (v3_yellow_6(esk1_3(X1,X2,X3),X1)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_66, plain, (l1_waybel_0(esk1_3(X1,X2,X3),X1)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_67, plain, (r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)|v2_struct_0(X1)|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,X2))|~r2_waybel_7(esk5_0,esk7_0,X1)|~r2_hidden(X2,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_59])])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (r2_waybel_7(esk5_0,esk7_0,esk8_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(X2)|~r1_waybel_0(esk5_0,X2,esk6_0)|~l1_waybel_0(X2,esk5_0)|~v3_yellow_6(X2,esk5_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~r2_hidden(X1,k10_yellow_6(esk5_0,X2))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_59])])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk5_0,esk1_3(esk5_0,esk6_0,X1)))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (v4_orders_2(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (v7_waybel_0(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (v3_yellow_6(esk1_3(esk5_0,esk6_0,X1),esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (l1_waybel_0(esk1_3(esk5_0,esk6_0,X1),esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (r1_waybel_0(esk5_0,esk1_3(esk5_0,esk6_0,X1),esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_8]), c_0_9]), c_0_10])]), c_0_11])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~r2_waybel_7(esk5_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_8]), c_0_69])])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (r2_waybel_7(esk5_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_59])])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_59])])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)|~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (r2_hidden(X1,esk6_0)|v2_struct_0(esk1_3(esk5_0,esk6_0,X1))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_77]), c_0_78])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (r2_hidden(esk8_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_59])])).
% 0.13/0.39  cnf(c_0_86, plain, (v2_struct_0(X1)|~v2_struct_0(esk1_3(X1,X2,X3))|~r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (v2_struct_0(esk1_3(esk5_0,esk6_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_81])]), c_0_85])).
% 0.13/0.39  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_84]), c_0_8]), c_0_81]), c_0_9]), c_0_10])]), c_0_11]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 89
% 0.13/0.39  # Proof object clause steps            : 80
% 0.13/0.39  # Proof object formula steps           : 9
% 0.13/0.39  # Proof object conjectures             : 57
% 0.13/0.39  # Proof object clause conjectures      : 54
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 40
% 0.13/0.39  # Proof object initial formulas used   : 4
% 0.13/0.39  # Proof object generating inferences   : 34
% 0.13/0.39  # Proof object simplifying inferences  : 151
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 4
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 40
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 40
% 0.13/0.39  # Processed clauses                    : 210
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 21
% 0.13/0.39  # ...remaining for further processing  : 189
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 47
% 0.13/0.39  # Generated clauses                    : 107
% 0.13/0.39  # ...of the previous two non-trivial   : 137
% 0.13/0.39  # Contextual simplify-reflections      : 24
% 0.13/0.39  # Paramodulations                      : 107
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 102
% 0.13/0.39  #    Positive orientable unit clauses  : 13
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 86
% 0.13/0.39  # Current number of unprocessed clauses: 7
% 0.13/0.39  # ...number of literals in the above   : 84
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 87
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 8544
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 404
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 45
% 0.13/0.39  # Unit Clause-clause subsumption calls : 506
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 2
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 12557
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.052 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.056 s
% 0.13/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
