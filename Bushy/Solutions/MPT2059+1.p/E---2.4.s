%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t18_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 265 expanded)
%              Number of clauses        :   35 (  84 expanded)
%              Number of leaves         :   11 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  405 (2190 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t4_subset)).

fof(dt_k10_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',dt_k10_yellow_6)).

fof(t18_yellow19,conjecture,(
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
             => ( r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))
              <=> r2_waybel_7(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t18_yellow19)).

fof(t13_yellow19,axiom,(
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
             => ( r2_hidden(X3,k10_yellow_6(X1,X2))
              <=> r2_waybel_7(X1,k2_yellow19(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t13_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t15_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',fc5_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',fc4_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',dt_k3_yellow19)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',dt_k2_struct_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',fc5_struct_0)).

fof(c_0_11,plain,(
    ! [X80,X81,X82] :
      ( ~ r2_hidden(X80,X81)
      | ~ m1_subset_1(X81,k1_zfmisc_1(X82))
      | m1_subset_1(X80,X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ v4_orders_2(X27)
      | ~ v7_waybel_0(X27)
      | ~ l1_waybel_0(X27,X26)
      | m1_subset_1(k10_yellow_6(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

fof(c_0_13,negated_conjecture,(
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
               => ( r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))
                <=> r2_waybel_7(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_yellow19])).

fof(c_0_14,plain,(
    ! [X66,X67,X68] :
      ( ( ~ r2_hidden(X68,k10_yellow_6(X66,X67))
        | r2_waybel_7(X66,k2_yellow19(X66,X67),X68)
        | ~ m1_subset_1(X68,u1_struct_0(X66))
        | v2_struct_0(X67)
        | ~ v4_orders_2(X67)
        | ~ v7_waybel_0(X67)
        | ~ l1_waybel_0(X67,X66)
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66) )
      & ( ~ r2_waybel_7(X66,k2_yellow19(X66,X67),X68)
        | r2_hidden(X68,k10_yellow_6(X66,X67))
        | ~ m1_subset_1(X68,u1_struct_0(X66))
        | v2_struct_0(X67)
        | ~ v4_orders_2(X67)
        | ~ v7_waybel_0(X67)
        | ~ l1_waybel_0(X67,X66)
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).

fof(c_0_15,plain,(
    ! [X69,X70] :
      ( v2_struct_0(X69)
      | ~ l1_struct_0(X69)
      | v1_xboole_0(X70)
      | ~ v1_subset_1(X70,u1_struct_0(k3_yellow_1(k2_struct_0(X69))))
      | ~ v2_waybel_0(X70,k3_yellow_1(k2_struct_0(X69)))
      | ~ v13_waybel_0(X70,k3_yellow_1(k2_struct_0(X69)))
      | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X69)))))
      | X70 = k2_yellow19(X69,k3_yellow19(X69,k2_struct_0(X69),X70)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_16,plain,(
    ! [X36] :
      ( ~ l1_pre_topc(X36)
      | l1_struct_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))
    & v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
      | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0) )
    & ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
      | r2_waybel_7(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_7(X1,k2_yellow19(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_waybel_7(X2,k2_yellow19(X2,X3),X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k10_yellow_6(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ r2_hidden(X1,k10_yellow_6(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,k3_yellow19(X2,k2_struct_0(X2),X3)))
    | v1_xboole_0(X3)
    | v2_struct_0(k3_yellow19(X2,k2_struct_0(X2),X3))
    | v2_struct_0(X2)
    | ~ v7_waybel_0(k3_yellow19(X2,k2_struct_0(X2),X3))
    | ~ v4_orders_2(k3_yellow19(X2,k2_struct_0(X2),X3))
    | ~ l1_waybel_0(k3_yellow19(X2,k2_struct_0(X2),X3),X2)
    | ~ r2_waybel_7(X2,X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,plain,
    ( r2_waybel_7(X1,X2,X3)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)
    | ~ r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_24]),c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
    | r2_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35])).

fof(c_0_39,plain,(
    ! [X95,X96,X97] :
      ( ( ~ v2_struct_0(k3_yellow19(X95,X96,X97))
        | v2_struct_0(X95)
        | ~ l1_struct_0(X95)
        | v1_xboole_0(X96)
        | ~ m1_subset_1(X96,k1_zfmisc_1(u1_struct_0(X95)))
        | v1_xboole_0(X97)
        | ~ v1_subset_1(X97,u1_struct_0(k3_yellow_1(X96)))
        | ~ v2_waybel_0(X97,k3_yellow_1(X96))
        | ~ v13_waybel_0(X97,k3_yellow_1(X96))
        | ~ m1_subset_1(X97,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X96)))) )
      & ( v6_waybel_0(k3_yellow19(X95,X96,X97),X95)
        | v2_struct_0(X95)
        | ~ l1_struct_0(X95)
        | v1_xboole_0(X96)
        | ~ m1_subset_1(X96,k1_zfmisc_1(u1_struct_0(X95)))
        | v1_xboole_0(X97)
        | ~ v1_subset_1(X97,u1_struct_0(k3_yellow_1(X96)))
        | ~ v2_waybel_0(X97,k3_yellow_1(X96))
        | ~ v13_waybel_0(X97,k3_yellow_1(X96))
        | ~ m1_subset_1(X97,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X96)))) )
      & ( v7_waybel_0(k3_yellow19(X95,X96,X97))
        | v2_struct_0(X95)
        | ~ l1_struct_0(X95)
        | v1_xboole_0(X96)
        | ~ m1_subset_1(X96,k1_zfmisc_1(u1_struct_0(X95)))
        | v1_xboole_0(X97)
        | ~ v1_subset_1(X97,u1_struct_0(k3_yellow_1(X96)))
        | ~ v2_waybel_0(X97,k3_yellow_1(X96))
        | ~ v13_waybel_0(X97,k3_yellow_1(X96))
        | ~ m1_subset_1(X97,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X96)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

cnf(c_0_40,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35]),c_0_38])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

fof(c_0_43,plain,(
    ! [X91,X92,X93] :
      ( ( ~ v2_struct_0(k3_yellow19(X91,X92,X93))
        | v2_struct_0(X91)
        | ~ l1_struct_0(X91)
        | v1_xboole_0(X92)
        | ~ m1_subset_1(X92,k1_zfmisc_1(u1_struct_0(X91)))
        | v1_xboole_0(X93)
        | ~ v2_waybel_0(X93,k3_yellow_1(X92))
        | ~ v13_waybel_0(X93,k3_yellow_1(X92))
        | ~ m1_subset_1(X93,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X92)))) )
      & ( v3_orders_2(k3_yellow19(X91,X92,X93))
        | v2_struct_0(X91)
        | ~ l1_struct_0(X91)
        | v1_xboole_0(X92)
        | ~ m1_subset_1(X92,k1_zfmisc_1(u1_struct_0(X91)))
        | v1_xboole_0(X93)
        | ~ v2_waybel_0(X93,k3_yellow_1(X92))
        | ~ v13_waybel_0(X93,k3_yellow_1(X92))
        | ~ m1_subset_1(X93,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X92)))) )
      & ( v4_orders_2(k3_yellow19(X91,X92,X93))
        | v2_struct_0(X91)
        | ~ l1_struct_0(X91)
        | v1_xboole_0(X92)
        | ~ m1_subset_1(X92,k1_zfmisc_1(u1_struct_0(X91)))
        | v1_xboole_0(X93)
        | ~ v2_waybel_0(X93,k3_yellow_1(X92))
        | ~ v13_waybel_0(X93,k3_yellow_1(X92))
        | ~ m1_subset_1(X93,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X92)))) )
      & ( v6_waybel_0(k3_yellow19(X91,X92,X93),X91)
        | v2_struct_0(X91)
        | ~ l1_struct_0(X91)
        | v1_xboole_0(X92)
        | ~ m1_subset_1(X92,k1_zfmisc_1(u1_struct_0(X91)))
        | v1_xboole_0(X93)
        | ~ v2_waybel_0(X93,k3_yellow_1(X92))
        | ~ v13_waybel_0(X93,k3_yellow_1(X92))
        | ~ m1_subset_1(X93,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X92)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_27]),c_0_29]),c_0_30]),c_0_31])]),c_0_34]),c_0_35])).

cnf(c_0_45,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_46,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v2_struct_0(k3_yellow19(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v1_xboole_0(X33)
        | ~ v2_waybel_0(X33,k3_yellow_1(X32))
        | ~ v13_waybel_0(X33,k3_yellow_1(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32)))) )
      & ( v6_waybel_0(k3_yellow19(X31,X32,X33),X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v1_xboole_0(X33)
        | ~ v2_waybel_0(X33,k3_yellow_1(X32))
        | ~ v13_waybel_0(X33,k3_yellow_1(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32)))) )
      & ( l1_waybel_0(k3_yellow19(X31,X32,X33),X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v1_xboole_0(X33)
        | ~ v2_waybel_0(X33,k3_yellow_1(X32))
        | ~ v13_waybel_0(X33,k3_yellow_1(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_42]),c_0_27]),c_0_29]),c_0_30])]),c_0_34]),c_0_35])).

cnf(c_0_48,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42]),c_0_27]),c_0_29]),c_0_30])]),c_0_34]),c_0_35])).

fof(c_0_51,plain,(
    ! [X28] :
      ( ~ l1_struct_0(X28)
      | m1_subset_1(k2_struct_0(X28),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_52,plain,(
    ! [X94] :
      ( v2_struct_0(X94)
      | ~ l1_struct_0(X94)
      | ~ v1_xboole_0(k2_struct_0(X94)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42]),c_0_27]),c_0_29]),c_0_30])]),c_0_34]),c_0_35])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_42])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_42])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
