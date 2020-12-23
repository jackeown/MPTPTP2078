%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:31 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 273 expanded)
%              Number of clauses        :   36 (  85 expanded)
%              Number of leaves         :    7 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  357 (2807 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   44 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
                      & v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
                      & v3_waybel_7(X4,k3_yellow_1(u1_struct_0(X1)))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))) )
                   => ~ ( r2_hidden(X2,X4)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X3)
                                & r2_waybel_7(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_7)).

fof(t32_waybel_7,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
                      & v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
                      & v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))) )
                   => ~ ( r2_hidden(X2,X4)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X3)
                                & r1_waybel_7(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_7)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc1_waybel_7,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & v3_waybel_7(X2,X1) )
           => ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(X1))
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_waybel_7)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(t31_waybel_7,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
            & v3_waybel_7(X2,k3_yellow_1(u1_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))) )
         => ! [X3] :
              ( r1_waybel_7(X1,X2,X3)
            <=> r2_waybel_7(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_7)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
               => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)
                 => ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
                        & v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
                        & v3_waybel_7(X4,k3_yellow_1(u1_struct_0(X1)))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))) )
                     => ~ ( r2_hidden(X2,X4)
                          & ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ~ ( r2_hidden(X5,X3)
                                  & r2_waybel_7(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_waybel_7])).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20] :
      ( ( m1_subset_1(esk2_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ r2_hidden(X18,X20)
        | v1_xboole_0(X20)
        | ~ v1_subset_1(X20,u1_struct_0(k3_yellow_1(u1_struct_0(X17))))
        | ~ v2_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))
        | ~ v13_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X17)))))
        | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X17)),X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))
        | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_4(X17,X18,X19,X20),X19)
        | ~ r2_hidden(X18,X20)
        | v1_xboole_0(X20)
        | ~ v1_subset_1(X20,u1_struct_0(k3_yellow_1(u1_struct_0(X17))))
        | ~ v2_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))
        | ~ v13_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X17)))))
        | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X17)),X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))
        | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_waybel_7(X17,X20,esk2_4(X17,X18,X19,X20))
        | ~ r2_hidden(X18,X20)
        | v1_xboole_0(X20)
        | ~ v1_subset_1(X20,u1_struct_0(k3_yellow_1(u1_struct_0(X17))))
        | ~ v2_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))
        | ~ v13_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X17)))))
        | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X17)),X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))
        | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_7])])])])])])).

fof(c_0_9,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ( ~ v1_xboole_0(X13)
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ v3_waybel_7(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( v1_subset_1(X13,u1_struct_0(X12))
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ v3_waybel_7(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( v2_waybel_0(X13,X12)
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ v3_waybel_7(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( v13_waybel_0(X13,X12)
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ v3_waybel_7(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_waybel_7])])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X26] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
      & m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
      & r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),esk4_0,esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0)))
      & v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0)))
      & v3_waybel_7(esk6_0,k3_yellow_1(u1_struct_0(esk3_0)))
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk3_0)))))
      & r2_hidden(esk4_0,esk6_0)
      & ( ~ m1_subset_1(X26,u1_struct_0(esk3_0))
        | ~ r2_hidden(X26,esk5_0)
        | ~ r2_waybel_7(esk3_0,esk6_0,X26) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

fof(c_0_12,plain,(
    ! [X11] :
      ( ~ v2_struct_0(k3_yellow_1(X11))
      & v1_orders_2(k3_yellow_1(X11))
      & v3_orders_2(k3_yellow_1(X11))
      & v4_orders_2(k3_yellow_1(X11))
      & v5_orders_2(k3_yellow_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_13,plain,(
    ! [X10] :
      ( v1_orders_2(k3_yellow_1(X10))
      & l1_orders_2(k3_yellow_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r1_waybel_7(X14,X15,X16)
        | r2_waybel_7(X14,X15,X16)
        | v1_xboole_0(X15)
        | ~ v2_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))
        | ~ v13_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))
        | ~ v3_waybel_7(X15,k3_yellow_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X14)))))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_waybel_7(X14,X15,X16)
        | r1_waybel_7(X14,X15,X16)
        | v1_xboole_0(X15)
        | ~ v2_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))
        | ~ v13_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))
        | ~ v3_waybel_7(X15,k3_yellow_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X14)))))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_7])])])])])).

cnf(c_0_15,plain,
    ( r1_waybel_7(X1,X2,esk2_4(X1,X3,X4,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_subset_1(X1,u1_struct_0(X2))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ v3_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v3_waybel_7(esk6_0,k3_yellow_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( v4_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v3_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_waybel_7(X1,X2,X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_7(X1,X2,X3)
    | ~ v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
    | ~ v3_waybel_7(X2,k3_yellow_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_waybel_7(X1,X2,esk2_4(X1,X3,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X3,X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))
    | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))
    | v1_xboole_0(X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X4)
    | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk6_0,X1)
    | ~ r1_waybel_7(esk3_0,esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_29]),c_0_30]),c_0_19]),c_0_20]),c_0_21])]),c_0_31]),c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_waybel_7(esk3_0,esk6_0,esk2_4(esk3_0,X1,X2,esk6_0))
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_29]),c_0_30]),c_0_33]),c_0_20]),c_0_21])]),c_0_31])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X3)
    | v1_xboole_0(X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X4)
    | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_waybel_7(esk3_0,esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk6_0,esk2_4(esk3_0,X1,X2,esk6_0))
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk2_4(esk3_0,X1,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_29]),c_0_30]),c_0_33]),c_0_20]),c_0_21])]),c_0_31])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk2_4(X1,X2,X3,X4),X3)
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ r2_hidden(esk2_4(esk3_0,X1,X2,esk6_0),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_4(esk3_0,X1,X2,esk6_0),X2)
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_29]),c_0_30]),c_0_33]),c_0_20]),c_0_21])]),c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_47,negated_conjecture,
    ( r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.042 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t33_waybel_7, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))=>(r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)=>![X4]:(((((~(v1_xboole_0(X4))&v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1))))&v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1))))&v3_waybel_7(X4,k3_yellow_1(u1_struct_0(X1))))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))))=>~((r2_hidden(X2,X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r2_hidden(X5,X3)&r2_waybel_7(X1,X4,X5))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_7)).
% 0.13/0.40  fof(t32_waybel_7, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))=>(r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)=>![X4]:(((((~(v1_xboole_0(X4))&v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))&v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1))))&v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1))))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))))=>~((r2_hidden(X2,X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r2_hidden(X5,X3)&r1_waybel_7(X1,X4,X5))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_7)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(cc1_waybel_7, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&v3_waybel_7(X2,X1))=>(((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(X1)))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_waybel_7)).
% 0.13/0.40  fof(fc7_yellow_1, axiom, ![X1]:((((~(v2_struct_0(k3_yellow_1(X1)))&v1_orders_2(k3_yellow_1(X1)))&v3_orders_2(k3_yellow_1(X1)))&v4_orders_2(k3_yellow_1(X1)))&v5_orders_2(k3_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_yellow_1)).
% 0.13/0.40  fof(dt_k3_yellow_1, axiom, ![X1]:(v1_orders_2(k3_yellow_1(X1))&l1_orders_2(k3_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_1)).
% 0.13/0.40  fof(t31_waybel_7, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1))))&v3_waybel_7(X2,k3_yellow_1(u1_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))))=>![X3]:(r1_waybel_7(X1,X2,X3)<=>r2_waybel_7(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_7)).
% 0.13/0.40  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))=>(r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)=>![X4]:(((((~(v1_xboole_0(X4))&v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1))))&v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1))))&v3_waybel_7(X4,k3_yellow_1(u1_struct_0(X1))))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1))))))=>~((r2_hidden(X2,X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r2_hidden(X5,X3)&r2_waybel_7(X1,X4,X5)))))))))))), inference(assume_negation,[status(cth)],[t33_waybel_7])).
% 0.13/0.40  fof(c_0_8, plain, ![X17, X18, X19, X20]:((m1_subset_1(esk2_4(X17,X18,X19,X20),u1_struct_0(X17))|~r2_hidden(X18,X20)|(v1_xboole_0(X20)|~v1_subset_1(X20,u1_struct_0(k3_yellow_1(u1_struct_0(X17))))|~v2_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))|~v13_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X17))))))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X17)),X18,X19)|~m1_subset_1(X19,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))|~m1_subset_1(X18,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((r2_hidden(esk2_4(X17,X18,X19,X20),X19)|~r2_hidden(X18,X20)|(v1_xboole_0(X20)|~v1_subset_1(X20,u1_struct_0(k3_yellow_1(u1_struct_0(X17))))|~v2_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))|~v13_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X17))))))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X17)),X18,X19)|~m1_subset_1(X19,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))|~m1_subset_1(X18,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(r1_waybel_7(X17,X20,esk2_4(X17,X18,X19,X20))|~r2_hidden(X18,X20)|(v1_xboole_0(X20)|~v1_subset_1(X20,u1_struct_0(k3_yellow_1(u1_struct_0(X17))))|~v2_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))|~v13_waybel_0(X20,k3_yellow_1(u1_struct_0(X17)))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X17))))))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X17)),X18,X19)|~m1_subset_1(X19,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))|~m1_subset_1(X18,u1_struct_0(k2_yellow_1(u1_pre_topc(X17))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_7])])])])])])).
% 0.13/0.40  fof(c_0_9, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_10, plain, ![X12, X13]:((((~v1_xboole_0(X13)|(v1_xboole_0(X13)|~v2_waybel_0(X13,X12)|~v13_waybel_0(X13,X12)|~v3_waybel_7(X13,X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))&(v1_subset_1(X13,u1_struct_0(X12))|(v1_xboole_0(X13)|~v2_waybel_0(X13,X12)|~v13_waybel_0(X13,X12)|~v3_waybel_7(X13,X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12))))&(v2_waybel_0(X13,X12)|(v1_xboole_0(X13)|~v2_waybel_0(X13,X12)|~v13_waybel_0(X13,X12)|~v3_waybel_7(X13,X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12))))&(v13_waybel_0(X13,X12)|(v1_xboole_0(X13)|~v2_waybel_0(X13,X12)|~v13_waybel_0(X13,X12)|~v3_waybel_7(X13,X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_waybel_7])])])])])).
% 0.13/0.40  fof(c_0_11, negated_conjecture, ![X26]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))&(m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))&(r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),esk4_0,esk5_0)&(((((~v1_xboole_0(esk6_0)&v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0))))&v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0))))&v3_waybel_7(esk6_0,k3_yellow_1(u1_struct_0(esk3_0))))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk3_0))))))&(r2_hidden(esk4_0,esk6_0)&(~m1_subset_1(X26,u1_struct_0(esk3_0))|(~r2_hidden(X26,esk5_0)|~r2_waybel_7(esk3_0,esk6_0,X26))))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).
% 0.20/0.40  fof(c_0_12, plain, ![X11]:((((~v2_struct_0(k3_yellow_1(X11))&v1_orders_2(k3_yellow_1(X11)))&v3_orders_2(k3_yellow_1(X11)))&v4_orders_2(k3_yellow_1(X11)))&v5_orders_2(k3_yellow_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).
% 0.20/0.40  fof(c_0_13, plain, ![X10]:(v1_orders_2(k3_yellow_1(X10))&l1_orders_2(k3_yellow_1(X10))), inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).
% 0.20/0.40  fof(c_0_14, plain, ![X14, X15, X16]:((~r1_waybel_7(X14,X15,X16)|r2_waybel_7(X14,X15,X16)|(v1_xboole_0(X15)|~v2_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))|~v13_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))|~v3_waybel_7(X15,k3_yellow_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X14))))))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r2_waybel_7(X14,X15,X16)|r1_waybel_7(X14,X15,X16)|(v1_xboole_0(X15)|~v2_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))|~v13_waybel_0(X15,k3_yellow_1(u1_struct_0(X14)))|~v3_waybel_7(X15,k3_yellow_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X14))))))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_7])])])])])).
% 0.20/0.40  cnf(c_0_15, plain, (r1_waybel_7(X1,X2,esk2_4(X1,X3,X4,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X3,X4)|~m1_subset_1(X4,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_16, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_17, plain, (v1_subset_1(X1,u1_struct_0(X2))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_waybel_0(X1,X2)|~v13_waybel_0(X1,X2)|~v3_waybel_7(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (v3_waybel_7(esk6_0,k3_yellow_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_22, plain, (v5_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_23, plain, (v4_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_24, plain, (v3_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_25, plain, (l1_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_26, plain, (~v2_struct_0(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_28, plain, (r2_waybel_7(X1,X2,X3)|v1_xboole_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,X2,X3)|~v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))|~v3_waybel_7(X2,k3_yellow_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_32, plain, (r1_waybel_7(X1,X2,esk2_4(X1,X3,X4,X2))|v2_struct_0(X1)|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X3,X4)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))|~v13_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))|~v2_waybel_0(X2,k3_yellow_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))|~m1_subset_1(X4,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 0.20/0.40  cnf(c_0_34, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))|v1_xboole_0(X4)|v2_struct_0(X1)|~r2_hidden(X2,X4)|~v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))|~v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (r2_waybel_7(esk3_0,esk6_0,X1)|~r1_waybel_7(esk3_0,esk6_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_29]), c_0_30]), c_0_19]), c_0_20]), c_0_21])]), c_0_31]), c_0_27])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (r1_waybel_7(esk3_0,esk6_0,esk2_4(esk3_0,X1,X2,esk6_0))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_29]), c_0_30]), c_0_33]), c_0_20]), c_0_21])]), c_0_31])).
% 0.20/0.40  cnf(c_0_37, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))|v2_struct_0(X1)|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))|~v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_34, c_0_16])).
% 0.20/0.40  cnf(c_0_38, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X3)|v1_xboole_0(X4)|v2_struct_0(X1)|~r2_hidden(X2,X4)|~v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))|~v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)|~r2_waybel_7(esk3_0,esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (r2_waybel_7(esk3_0,esk6_0,esk2_4(esk3_0,X1,X2,esk6_0))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk2_4(esk3_0,X1,X2,esk6_0),u1_struct_0(esk3_0))|~r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_29]), c_0_30]), c_0_33]), c_0_20]), c_0_21])]), c_0_31])).
% 0.20/0.40  cnf(c_0_42, plain, (v2_struct_0(X1)|r2_hidden(esk2_4(X1,X2,X3,X4),X3)|~r1_waybel_3(k2_yellow_1(u1_pre_topc(X1)),X2,X3)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))|~v13_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~v2_waybel_0(X4,k3_yellow_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X1)))))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_38, c_0_16])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (~r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~r2_hidden(esk2_4(esk3_0,X1,X2,esk6_0),esk5_0)|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_4(esk3_0,X1,X2,esk6_0),X2)|~r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_18]), c_0_29]), c_0_30]), c_0_33]), c_0_20]), c_0_21])]), c_0_31])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (~r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (r1_waybel_3(k2_yellow_1(u1_pre_topc(esk3_0)),esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 51
% 0.20/0.40  # Proof object clause steps            : 36
% 0.20/0.40  # Proof object formula steps           : 15
% 0.20/0.40  # Proof object conjectures             : 25
% 0.20/0.40  # Proof object clause conjectures      : 22
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 24
% 0.20/0.40  # Proof object initial formulas used   : 7
% 0.20/0.40  # Proof object generating inferences   : 9
% 0.20/0.40  # Proof object simplifying inferences  : 48
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 7
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 31
% 0.20/0.40  # Removed in clause preprocessing      : 3
% 0.20/0.40  # Initial clauses in saturation        : 28
% 0.20/0.40  # Processed clauses                    : 68
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 1
% 0.20/0.40  # ...remaining for further processing  : 66
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 16
% 0.20/0.40  # ...of the previous two non-trivial   : 13
% 0.20/0.40  # Contextual simplify-reflections      : 4
% 0.20/0.40  # Paramodulations                      : 16
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 39
% 0.20/0.40  #    Positive orientable unit clauses  : 17
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 4
% 0.20/0.40  #    Non-unit-clauses                  : 18
% 0.20/0.40  # Current number of unprocessed clauses: 0
% 0.20/0.40  # ...number of literals in the above   : 0
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 27
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 230
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 8
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.40  # Unit Clause-clause subsumption calls : 6
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 0
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 4224
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.045 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.050 s
% 0.20/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
