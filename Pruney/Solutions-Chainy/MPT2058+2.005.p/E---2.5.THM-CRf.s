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
% DateTime   : Thu Dec  3 11:21:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 (1797 expanded)
%              Number of clauses        :   67 ( 674 expanded)
%              Number of leaves         :   14 ( 450 expanded)
%              Depth                    :   15
%              Number of atoms          :  494 (10606 expanded)
%              Number of equality atoms :   17 ( 430 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t30_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | m1_subset_1(k1_connsp_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v2_struct_0(k3_yellow19(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) )
      & ( v3_orders_2(k3_yellow19(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) )
      & ( v4_orders_2(k3_yellow19(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) )
      & ( v6_waybel_0(k3_yellow19(X21,X22,X23),X21)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

fof(c_0_18,plain,(
    ! [X17] : k3_yellow_1(X17) = k3_lattice3(k1_lattice3(X17)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_19,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | ~ v1_xboole_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | r2_hidden(X16,k1_connsp_2(X15,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).

fof(c_0_26,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | v1_xboole_0(X31)
      | ~ v1_subset_1(X31,u1_struct_0(k3_yellow_1(k2_struct_0(X30))))
      | ~ v2_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))
      | ~ v13_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X30)))))
      | X31 = k2_yellow19(X30,k3_yellow19(X30,k2_struct_0(X30),X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_27,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_28,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_37,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v2_struct_0(k3_yellow19(X24,X25,X26))
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( v6_waybel_0(k3_yellow19(X24,X25,X26),X24)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( v7_waybel_0(k3_yellow19(X24,X25,X26))
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_38,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r3_waybel_9(X27,X28,X29)
        | r1_waybel_7(X27,k2_yellow19(X27,X28),X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_waybel_7(X27,k2_yellow19(X27,X28),X29)
        | r3_waybel_9(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_47,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | k2_struct_0(X11) = u1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k1_connsp_2(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,k1_connsp_2(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_50,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_53,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_struct_0(k3_yellow19(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( v6_waybel_0(k3_yellow19(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( l1_waybel_0(k3_yellow19(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_56,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_59,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_64,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( r1_waybel_7(esk1_0,k2_yellow19(esk1_0,X1),esk3_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_56]),c_0_44]),c_0_45])]),c_0_24]),c_0_46]),c_0_57])])).

cnf(c_0_68,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_57])]),c_0_60])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_43]),c_0_56]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_73,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_74,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_57])]),c_0_24])).

cnf(c_0_75,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_59]),c_0_57])]),c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_78,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_59]),c_0_74]),c_0_57])])).

cnf(c_0_79,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_69]),c_0_57])]),c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0),X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_59]),c_0_57])]),c_0_60])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_82,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_69]),c_0_57])]),c_0_24])).

cnf(c_0_84,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_85,negated_conjecture,
    ( k2_yellow19(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_59]),c_0_57])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_87,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_59]),c_0_57])]),c_0_60])).

cnf(c_0_88,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_89,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),X1)
    | v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,X1)
    | ~ l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_22]),c_0_23])]),c_0_24]),c_0_79]),c_0_74])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_59]),c_0_57])])).

cnf(c_0_91,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_57]),c_0_69])]),c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),X1)
    | v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_83])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_94,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_91]),c_0_21])]),c_0_93])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_94]),c_0_57]),c_0_69])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.031 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 0.19/0.38  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.19/0.38  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.19/0.38  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.19/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.38  fof(t30_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_hidden(X2,k1_connsp_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 0.19/0.38  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.19/0.38  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 0.19/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.19/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.19/0.38  fof(c_0_15, plain, ![X13, X14]:(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_subset_1(X14,u1_struct_0(X13))|m1_subset_1(k1_connsp_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((((~v1_xboole_0(esk2_0)&v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))&v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&((~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0))&(r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.38  fof(c_0_17, plain, ![X21, X22, X23]:((((~v2_struct_0(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22))))))&(v3_orders_2(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))))))&(v4_orders_2(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))))))&(v6_waybel_0(k3_yellow19(X21,X22,X23),X21)|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.19/0.38  fof(c_0_18, plain, ![X17]:k3_yellow_1(X17)=k3_lattice3(k1_lattice3(X17)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.19/0.38  fof(c_0_19, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|~v1_xboole_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.38  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_25, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|r2_hidden(X16,k1_connsp_2(X15,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).
% 0.19/0.38  fof(c_0_26, plain, ![X30, X31]:(v2_struct_0(X30)|~l1_struct_0(X30)|(v1_xboole_0(X31)|~v1_subset_1(X31,u1_struct_0(k3_yellow_1(k2_struct_0(X30))))|~v2_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))|~v13_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X30)))))|X31=k2_yellow19(X30,k3_yellow19(X30,k2_struct_0(X30),X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.19/0.38  fof(c_0_27, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_28, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_29, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (m1_subset_1(k1_connsp_2(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.38  cnf(c_0_35, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_connsp_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_36, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_37, plain, ![X24, X25, X26]:(((~v2_struct_0(k3_yellow19(X24,X25,X26))|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))&(v6_waybel_0(k3_yellow19(X24,X25,X26),X24)|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))))))&(v7_waybel_0(k3_yellow19(X24,X25,X26))|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.19/0.38  fof(c_0_38, plain, ![X27, X28, X29]:((~r3_waybel_9(X27,X28,X29)|r1_waybel_7(X27,k2_yellow19(X27,X28),X29)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~r1_waybel_7(X27,k2_yellow19(X27,X28),X29)|r3_waybel_9(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.19/0.38  cnf(c_0_39, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_42, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))))), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_31, c_0_29])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_32, c_0_29])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_47, plain, ![X11]:(~l1_struct_0(X11)|k2_struct_0(X11)=u1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk1_0))|~r2_hidden(X1,k1_connsp_2(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_0,k1_connsp_2(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.38  fof(c_0_50, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_51, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.38  cnf(c_0_52, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  fof(c_0_53, plain, ![X18, X19, X20]:(((~v2_struct_0(k3_yellow19(X18,X19,X20))|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))&(v6_waybel_0(k3_yellow19(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))))))&(l1_waybel_0(k3_yellow19(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.19/0.38  cnf(c_0_54, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_55, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))), inference(rw,[status(thm)],[c_0_40, c_0_29])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_41, c_0_23])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.19/0.38  cnf(c_0_59, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.38  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.38  cnf(c_0_63, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.38  cnf(c_0_64, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (r1_waybel_7(esk1_0,k2_yellow19(esk1_0,X1),esk3_0)|v2_struct_0(X1)|~r3_waybel_9(esk1_0,X1,esk3_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_43]), c_0_56]), c_0_44]), c_0_45])]), c_0_24]), c_0_46]), c_0_57])])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (v4_orders_2(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_57])]), c_0_60])).
% 0.19/0.38  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_43]), c_0_56]), c_0_44]), c_0_45])]), c_0_46])).
% 0.19/0.38  cnf(c_0_71, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.38  cnf(c_0_72, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (v4_orders_2(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_57])]), c_0_24])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_59]), c_0_57])]), c_0_60])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.19/0.38  cnf(c_0_77, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_59]), c_0_74]), c_0_57])])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (v7_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_69]), c_0_57])]), c_0_24])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0),X1)|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_59]), c_0_57])]), c_0_60])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk1_0))|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_69]), c_0_57])]), c_0_24])).
% 0.19/0.38  cnf(c_0_84, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (k2_yellow19(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_59]), c_0_57])])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_59]), c_0_57])]), c_0_60])).
% 0.19/0.38  cnf(c_0_88, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.19/0.38  cnf(c_0_89, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),X1)|v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,X1)|~l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_22]), c_0_23])]), c_0_24]), c_0_79]), c_0_74])])).
% 0.19/0.38  cnf(c_0_90, negated_conjecture, (~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_59]), c_0_57])])).
% 0.19/0.38  cnf(c_0_91, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_57]), c_0_69])]), c_0_24])).
% 0.19/0.38  cnf(c_0_92, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),X1)|v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_83])])).
% 0.19/0.38  cnf(c_0_93, negated_conjecture, (~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.19/0.38  cnf(c_0_94, negated_conjecture, (v2_struct_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_91]), c_0_21])]), c_0_93])).
% 0.19/0.38  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_94]), c_0_57]), c_0_69])]), c_0_24]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 96
% 0.19/0.38  # Proof object clause steps            : 67
% 0.19/0.38  # Proof object formula steps           : 29
% 0.19/0.38  # Proof object conjectures             : 48
% 0.19/0.38  # Proof object clause conjectures      : 45
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 26
% 0.19/0.38  # Proof object initial formulas used   : 14
% 0.19/0.38  # Proof object generating inferences   : 27
% 0.19/0.38  # Proof object simplifying inferences  : 115
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 14
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 35
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 34
% 0.19/0.38  # Processed clauses                    : 126
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 29
% 0.19/0.38  # ...remaining for further processing  : 96
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 11
% 0.19/0.38  # Generated clauses                    : 92
% 0.19/0.38  # ...of the previous two non-trivial   : 93
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 88
% 0.19/0.38  # Factorizations                       : 2
% 0.19/0.38  # Equation resolutions                 : 2
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
% 0.19/0.38  # Current number of processed clauses  : 82
% 0.19/0.38  #    Positive orientable unit clauses  : 25
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 6
% 0.19/0.38  #    Non-unit-clauses                  : 51
% 0.19/0.38  # Current number of unprocessed clauses: 1
% 0.19/0.38  # ...number of literals in the above   : 4
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 13
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1593
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 157
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 29
% 0.19/0.38  # Unit Clause-clause subsumption calls : 118
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 20
% 0.19/0.38  # BW rewrite match successes           : 4
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7803
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.008 s
% 0.19/0.38  # Total time               : 0.045 s
% 0.19/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
