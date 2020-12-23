%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t17_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:49 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 262 expanded)
%              Number of clauses        :   32 (  82 expanded)
%              Number of leaves         :    9 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  364 (2185 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_waybel_9(X1,X2,X3)
              <=> r1_waybel_7(X1,k2_yellow19(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',t12_yellow19)).

fof(t15_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',t15_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',dt_l1_pre_topc)).

fof(t17_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
              <=> r1_waybel_7(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',t17_yellow19)).

fof(fc5_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1)
        & v7_waybel_0(k3_yellow19(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',fc5_yellow19)).

fof(fc4_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v3_orders_2(k3_yellow19(X1,X2,X3))
        & v4_orders_2(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',fc4_yellow19)).

fof(dt_k3_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1)
        & l1_waybel_0(k3_yellow19(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',dt_k3_yellow19)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',fc5_struct_0)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',dt_k2_struct_0)).

fof(c_0_9,plain,(
    ! [X64,X65,X66] :
      ( ( ~ r3_waybel_9(X64,X65,X66)
        | r1_waybel_7(X64,k2_yellow19(X64,X65),X66)
        | ~ m1_subset_1(X66,u1_struct_0(X64))
        | v2_struct_0(X65)
        | ~ v4_orders_2(X65)
        | ~ v7_waybel_0(X65)
        | ~ l1_waybel_0(X65,X64)
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) )
      & ( ~ r1_waybel_7(X64,k2_yellow19(X64,X65),X66)
        | r3_waybel_9(X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X64))
        | v2_struct_0(X65)
        | ~ v4_orders_2(X65)
        | ~ v7_waybel_0(X65)
        | ~ l1_waybel_0(X65,X64)
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

fof(c_0_10,plain,(
    ! [X67,X68] :
      ( v2_struct_0(X67)
      | ~ l1_struct_0(X67)
      | v1_xboole_0(X68)
      | ~ v1_subset_1(X68,u1_struct_0(k3_yellow_1(k2_struct_0(X67))))
      | ~ v2_waybel_0(X68,k3_yellow_1(k2_struct_0(X67)))
      | ~ v13_waybel_0(X68,k3_yellow_1(k2_struct_0(X67)))
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X67)))))
      | X68 = k2_yellow19(X67,k3_yellow19(X67,k2_struct_0(X67),X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_11,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
                <=> r1_waybel_7(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_yellow19])).

cnf(c_0_13,plain,
    ( r1_waybel_7(X1,k2_yellow19(X1,X2),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))
    & v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
      | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0) )
    & ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
      | r1_waybel_7(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_17,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_7(X1,k2_yellow19(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r1_waybel_7(X1,X2,X3)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)
    | ~ r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)
    | ~ r1_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

fof(c_0_32,plain,(
    ! [X93,X94,X95] :
      ( ( ~ v2_struct_0(k3_yellow19(X93,X94,X95))
        | v2_struct_0(X93)
        | ~ l1_struct_0(X93)
        | v1_xboole_0(X94)
        | ~ m1_subset_1(X94,k1_zfmisc_1(u1_struct_0(X93)))
        | v1_xboole_0(X95)
        | ~ v1_subset_1(X95,u1_struct_0(k3_yellow_1(X94)))
        | ~ v2_waybel_0(X95,k3_yellow_1(X94))
        | ~ v13_waybel_0(X95,k3_yellow_1(X94))
        | ~ m1_subset_1(X95,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X94)))) )
      & ( v6_waybel_0(k3_yellow19(X93,X94,X95),X93)
        | v2_struct_0(X93)
        | ~ l1_struct_0(X93)
        | v1_xboole_0(X94)
        | ~ m1_subset_1(X94,k1_zfmisc_1(u1_struct_0(X93)))
        | v1_xboole_0(X95)
        | ~ v1_subset_1(X95,u1_struct_0(k3_yellow_1(X94)))
        | ~ v2_waybel_0(X95,k3_yellow_1(X94))
        | ~ v13_waybel_0(X95,k3_yellow_1(X94))
        | ~ m1_subset_1(X95,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X94)))) )
      & ( v7_waybel_0(k3_yellow19(X93,X94,X95))
        | v2_struct_0(X93)
        | ~ l1_struct_0(X93)
        | v1_xboole_0(X94)
        | ~ m1_subset_1(X94,k1_zfmisc_1(u1_struct_0(X93)))
        | v1_xboole_0(X95)
        | ~ v1_subset_1(X95,u1_struct_0(k3_yellow_1(X94)))
        | ~ v2_waybel_0(X95,k3_yellow_1(X94))
        | ~ v13_waybel_0(X95,k3_yellow_1(X94))
        | ~ m1_subset_1(X95,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X94)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

cnf(c_0_33,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28]),c_0_31])).

cnf(c_0_34,plain,
    ( v7_waybel_0(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_25])).

fof(c_0_36,plain,(
    ! [X89,X90,X91] :
      ( ( ~ v2_struct_0(k3_yellow19(X89,X90,X91))
        | v2_struct_0(X89)
        | ~ l1_struct_0(X89)
        | v1_xboole_0(X90)
        | ~ m1_subset_1(X90,k1_zfmisc_1(u1_struct_0(X89)))
        | v1_xboole_0(X91)
        | ~ v2_waybel_0(X91,k3_yellow_1(X90))
        | ~ v13_waybel_0(X91,k3_yellow_1(X90))
        | ~ m1_subset_1(X91,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X90)))) )
      & ( v3_orders_2(k3_yellow19(X89,X90,X91))
        | v2_struct_0(X89)
        | ~ l1_struct_0(X89)
        | v1_xboole_0(X90)
        | ~ m1_subset_1(X90,k1_zfmisc_1(u1_struct_0(X89)))
        | v1_xboole_0(X91)
        | ~ v2_waybel_0(X91,k3_yellow_1(X90))
        | ~ v13_waybel_0(X91,k3_yellow_1(X90))
        | ~ m1_subset_1(X91,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X90)))) )
      & ( v4_orders_2(k3_yellow19(X89,X90,X91))
        | v2_struct_0(X89)
        | ~ l1_struct_0(X89)
        | v1_xboole_0(X90)
        | ~ m1_subset_1(X90,k1_zfmisc_1(u1_struct_0(X89)))
        | v1_xboole_0(X91)
        | ~ v2_waybel_0(X91,k3_yellow_1(X90))
        | ~ v13_waybel_0(X91,k3_yellow_1(X90))
        | ~ m1_subset_1(X91,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X90)))) )
      & ( v6_waybel_0(k3_yellow19(X89,X90,X91),X89)
        | v2_struct_0(X89)
        | ~ l1_struct_0(X89)
        | v1_xboole_0(X90)
        | ~ m1_subset_1(X90,k1_zfmisc_1(u1_struct_0(X89)))
        | v1_xboole_0(X91)
        | ~ v2_waybel_0(X91,k3_yellow_1(X90))
        | ~ v13_waybel_0(X91,k3_yellow_1(X90))
        | ~ m1_subset_1(X91,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X90)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_20]),c_0_22]),c_0_23]),c_0_24])]),c_0_27]),c_0_28])).

cnf(c_0_38,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_39,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v2_struct_0(k3_yellow19(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,k3_yellow_1(X30))
        | ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( v6_waybel_0(k3_yellow19(X29,X30,X31),X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,k3_yellow_1(X30))
        | ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( l1_waybel_0(k3_yellow19(X29,X30,X31),X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,k3_yellow_1(X30))
        | ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_35]),c_0_20]),c_0_22]),c_0_23])]),c_0_27]),c_0_28])).

cnf(c_0_41,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_42,plain,(
    ! [X92] :
      ( v2_struct_0(X92)
      | ~ l1_struct_0(X92)
      | ~ v1_xboole_0(k2_struct_0(X92)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35]),c_0_20]),c_0_22]),c_0_23])]),c_0_27]),c_0_28])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35]),c_0_20]),c_0_22]),c_0_23])]),c_0_27]),c_0_28])).

fof(c_0_47,plain,(
    ! [X26] :
      ( ~ l1_struct_0(X26)
      | m1_subset_1(k2_struct_0(X26),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_35])]),c_0_28])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
