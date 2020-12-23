%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:09 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 190 expanded)
%              Number of clauses        :   38 (  79 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 588 expanded)
%              Number of equality atoms :   22 (  56 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(t5_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_waybel_7(X1,k1_yellow19(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k1_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow19)).

fof(fc1_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k1_yellow19(X1,X2))
        & v1_subset_1(k1_yellow19(X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
        & v2_waybel_0(k1_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
        & v13_waybel_0(k1_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow19)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(t4_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
             => ( r2_waybel_7(X1,X3,X2)
              <=> r1_tarski(k1_yellow19(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21] :
      ( ( X18 = X20
        | g1_orders_2(X18,X19) != g1_orders_2(X20,X21)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18))) )
      & ( X19 = X21
        | g1_orders_2(X18,X19) != g1_orders_2(X20,X21)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_14,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | m1_subset_1(u1_orders_2(X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X13)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ( v1_orders_2(g1_orders_2(X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) )
      & ( l1_orders_2(g1_orders_2(X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r2_waybel_7(X1,k1_yellow19(X1,X2),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t5_yellow19])).

cnf(c_0_20,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | k2_struct_0(X6) = u1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_25,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_26,plain,(
    ! [X9,X10] :
      ( v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | m1_subset_1(k1_yellow19(X9,X10),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X9))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_yellow19])])])).

fof(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ~ r2_waybel_7(esk2_0,k1_yellow19(esk2_0,esk3_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ( ~ v1_xboole_0(k1_yellow19(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16)) )
      & ( v1_subset_1(k1_yellow19(X16,X17),u1_struct_0(k3_yellow_1(k2_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16)) )
      & ( v2_waybel_0(k1_yellow19(X16,X17),k3_yellow_1(k2_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16)) )
      & ( v13_waybel_0(k1_yellow19(X16,X17),k3_yellow_1(k2_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_yellow19])])])])).

fof(c_0_29,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | m1_subset_1(k2_struct_0(X11),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_30,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_31,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_32,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_33,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_waybel_7(X24,X26,X25)
        | r1_tarski(k1_yellow19(X24,X25),X26)
        | ~ v13_waybel_0(X26,k3_yellow_1(k2_struct_0(X24)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X24)))))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ r1_tarski(k1_yellow19(X24,X25),X26)
        | r2_waybel_7(X24,X26,X25)
        | ~ v13_waybel_0(X26,k3_yellow_1(k2_struct_0(X24)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X24)))))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_yellow19])])])])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( v13_waybel_0(k1_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_44,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_45,plain,(
    ! [X14] : m1_subset_1(esk1_1(X14),X14) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_46,plain,
    ( r2_waybel_7(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ r1_tarski(k1_yellow19(X1,X2),X3)
    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k1_yellow19(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v13_waybel_0(k1_yellow19(esk2_0,esk3_0),k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

fof(c_0_49,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k2_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( k2_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) = u1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_waybel_7(esk2_0,k1_yellow19(esk2_0,esk3_0),X1)
    | ~ r1_tarski(k1_yellow19(esk2_0,X1),k1_yellow19(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( m1_subset_1(u1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( v1_orders_2(g1_orders_2(X1,esk1_1(k1_zfmisc_1(k2_zfmisc_1(X1,X1))))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_52])).

cnf(c_0_57,plain,
    ( l1_orders_2(g1_orders_2(X1,esk1_1(k1_zfmisc_1(k2_zfmisc_1(X1,X1))))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_waybel_7(esk2_0,k1_yellow19(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( r2_waybel_7(esk2_0,k1_yellow19(esk2_0,esk3_0),X1)
    | ~ m1_subset_1(k1_yellow19(esk2_0,X1),k1_zfmisc_1(k1_yellow19(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_21]),c_0_34])).

cnf(c_0_61,plain,
    ( u1_struct_0(g1_orders_2(X1,esk1_1(k1_zfmisc_1(k2_zfmisc_1(X1,X1))))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_56]),c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k1_yellow19(esk2_0,esk3_0),k1_zfmisc_1(k1_yellow19(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_37])])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_61]),c_0_61]),c_0_57])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),
    [proof]).

%------------------------------------------------------------------------------
