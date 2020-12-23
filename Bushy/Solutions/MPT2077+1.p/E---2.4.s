%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t37_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:52 EDT 2019

% Result     : Theorem 224.35s
% Output     : CNFRefutation 224.35s
% Verified   : 
% Statistics : Number of formulae       :  116 (4516 expanded)
%              Number of clauses        :   85 (1546 expanded)
%              Number of leaves         :   16 (1158 expanded)
%              Depth                    :   31
%              Number of atoms          :  737 (43709 expanded)
%              Number of equality atoms :   16 ( 207 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   44 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t4_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t6_boole)).

fof(t37_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ? [X3] :
                ( m2_yellow_6(X3,X1,X2)
                & v3_yellow_6(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t37_yellow19)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',d2_xboole_0)).

fof(d19_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( v3_yellow_6(X2,X1)
          <=> k10_yellow_6(X1,X2) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',d19_yellow_6)).

fof(t32_waybel_9,axiom,(
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
             => ~ ( r3_waybel_9(X1,X2,X3)
                  & ! [X4] :
                      ( m2_yellow_6(X4,X1,X2)
                     => ~ r2_hidden(X3,k10_yellow_6(X1,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t32_waybel_9)).

fof(dt_m2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m2_yellow_6(X3,X1,X2)
         => ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',dt_m2_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',dt_l1_pre_topc)).

fof(t35_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t35_yellow19)).

fof(t31_waybel_9,axiom,(
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
              ( m2_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r3_waybel_9(X1,X3,X4)
                   => r3_waybel_9(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t31_waybel_9)).

fof(t29_waybel_9,axiom,(
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
               => r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',t29_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t37_yellow19.p',dt_k10_yellow_6)).

fof(c_0_16,plain,(
    ! [X61,X62,X63] :
      ( ~ r2_hidden(X61,X62)
      | ~ m1_subset_1(X62,k1_zfmisc_1(X63))
      | ~ v1_xboole_0(X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X31] : m1_subset_1(esk8_1(X31),X31) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_18,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X41,X42)
      | v1_xboole_0(X42)
      | r2_hidden(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X58,X59,X60] :
      ( ~ r2_hidden(X58,X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(X60))
      | m1_subset_1(X58,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_23,plain,(
    ! [X64] :
      ( ~ v1_xboole_0(X64)
      | X64 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk8_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,esk8_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_30,plain,
    ( esk8_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | m1_subset_1(esk8_1(esk8_1(k1_zfmisc_1(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_compts_1(X1)
        <=> ! [X2] :
              ( ( ~ v2_struct_0(X2)
                & v4_orders_2(X2)
                & v7_waybel_0(X2)
                & l1_waybel_0(X2,X1) )
             => ? [X3] :
                  ( m2_yellow_6(X3,X1,X2)
                  & v3_yellow_6(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_yellow19])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_34,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | r2_hidden(esk8_1(esk8_1(k1_zfmisc_1(X1))),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_31]),c_0_28])).

cnf(c_0_35,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_36,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

fof(c_0_37,negated_conjecture,(
    ! [X7,X8] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ( ~ v2_struct_0(esk2_0)
        | ~ v1_compts_1(esk1_0) )
      & ( v4_orders_2(esk2_0)
        | ~ v1_compts_1(esk1_0) )
      & ( v7_waybel_0(esk2_0)
        | ~ v1_compts_1(esk1_0) )
      & ( l1_waybel_0(esk2_0,esk1_0)
        | ~ v1_compts_1(esk1_0) )
      & ( ~ m2_yellow_6(X7,esk1_0,esk2_0)
        | ~ v3_yellow_6(X7,esk1_0)
        | ~ v1_compts_1(esk1_0) )
      & ( m2_yellow_6(esk3_1(X8),esk1_0,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,esk1_0)
        | v1_compts_1(esk1_0) )
      & ( v3_yellow_6(esk3_1(X8),esk1_0)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,esk1_0)
        | v1_compts_1(esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_32])])])])])])).

fof(c_0_38,plain,(
    ! [X12,X13] :
      ( ( ~ v3_yellow_6(X13,X12)
        | k10_yellow_6(X12,X13) != k1_xboole_0
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( k10_yellow_6(X12,X13) = k1_xboole_0
        | v3_yellow_6(X13,X12)
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk1_0,esk2_0)
    | ~ v3_yellow_6(X1,esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X47,X48,X49] :
      ( ( m2_yellow_6(esk10_3(X47,X48,X49),X47,X48)
        | ~ r3_waybel_9(X47,X48,X49)
        | ~ m1_subset_1(X49,u1_struct_0(X47))
        | v2_struct_0(X48)
        | ~ v4_orders_2(X48)
        | ~ v7_waybel_0(X48)
        | ~ l1_waybel_0(X48,X47)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( r2_hidden(X49,k10_yellow_6(X47,esk10_3(X47,X48,X49)))
        | ~ r3_waybel_9(X47,X48,X49)
        | ~ m1_subset_1(X49,u1_struct_0(X47))
        | v2_struct_0(X48)
        | ~ v4_orders_2(X48)
        | ~ v7_waybel_0(X48)
        | ~ l1_waybel_0(X48,X47)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k10_yellow_6(esk1_0,X1) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk1_0,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_49,plain,
    ( m2_yellow_6(esk10_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( v4_orders_2(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( v7_waybel_0(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,plain,
    ( esk8_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_47])).

fof(c_0_55,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v2_struct_0(X22)
        | ~ m2_yellow_6(X22,X20,X21)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20) )
      & ( v4_orders_2(X22)
        | ~ m2_yellow_6(X22,X20,X21)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20) )
      & ( v7_waybel_0(X22)
        | ~ m2_yellow_6(X22,X20,X21)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20) )
      & ( l1_waybel_0(X22,X20)
        | ~ m2_yellow_6(X22,X20,X21)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

fof(c_0_56,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk10_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( k10_yellow_6(esk1_0,esk10_3(esk1_0,esk2_0,X1)) = k1_xboole_0
    | v2_struct_0(esk10_3(esk1_0,esk2_0,X1))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_waybel_0(esk10_3(esk1_0,esk2_0,X1),esk1_0)
    | ~ v7_waybel_0(esk10_3(esk1_0,esk2_0,X1))
    | ~ v4_orders_2(esk10_3(esk1_0,esk2_0,X1))
    | ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_43]),c_0_44])]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_54]),c_0_40])])).

cnf(c_0_60,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(esk10_3(esk1_0,esk2_0,X1))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_waybel_0(esk10_3(esk1_0,esk2_0,X1),esk1_0)
    | ~ v7_waybel_0(esk10_3(esk1_0,esk2_0,X1))
    | ~ v4_orders_2(esk10_3(esk1_0,esk2_0,X1))
    | ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_43]),c_0_44])]),c_0_59]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_63,plain,
    ( v7_waybel_0(esk10_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_61])).

cnf(c_0_64,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(esk10_3(esk1_0,esk2_0,X1))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_waybel_0(esk10_3(esk1_0,esk2_0,X1),esk1_0)
    | ~ v4_orders_2(esk10_3(esk1_0,esk2_0,X1))
    | ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_43]),c_0_44])]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_66,plain,
    ( v4_orders_2(esk10_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_49]),c_0_61])).

cnf(c_0_67,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(esk10_3(esk1_0,esk2_0,X1))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_waybel_0(esk10_3(esk1_0,esk2_0,X1),esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_43]),c_0_44])]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_70,plain,
    ( l1_waybel_0(esk10_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_49]),c_0_61])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk10_3(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_49]),c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( v2_struct_0(esk10_3(esk1_0,esk2_0,X1))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_43]),c_0_44])]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

fof(c_0_73,plain,(
    ! [X51,X52,X55] :
      ( ( m1_subset_1(esk11_2(X51,X52),u1_struct_0(X51))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ v7_waybel_0(X52)
        | ~ l1_waybel_0(X52,X51)
        | ~ v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( r3_waybel_9(X51,X52,esk11_2(X51,X52))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ v7_waybel_0(X52)
        | ~ l1_waybel_0(X52,X51)
        | ~ v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( ~ v2_struct_0(esk12_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( v4_orders_2(esk12_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( v7_waybel_0(esk12_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( l1_waybel_0(esk12_1(X51),X51)
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( ~ m1_subset_1(X55,u1_struct_0(X51))
        | ~ r3_waybel_9(X51,esk12_1(X51),X55)
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_74,plain,(
    ! [X43,X44,X45,X46] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | v2_struct_0(X44)
      | ~ v4_orders_2(X44)
      | ~ v7_waybel_0(X44)
      | ~ l1_waybel_0(X44,X43)
      | ~ m2_yellow_6(X45,X43,X44)
      | ~ m1_subset_1(X46,u1_struct_0(X43))
      | ~ r3_waybel_9(X43,X45,X46)
      | r3_waybel_9(X43,X44,X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_75,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | v2_struct_0(X39)
      | ~ v4_orders_2(X39)
      | ~ v7_waybel_0(X39)
      | ~ l1_waybel_0(X39,X38)
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | ~ r2_hidden(X40,k10_yellow_6(X38,X39))
      | r3_waybel_9(X38,X39,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_43]),c_0_44])]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_77,plain,
    ( r3_waybel_9(X1,X2,esk11_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r3_waybel_9(X1,X2,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( m2_yellow_6(esk3_1(X1),esk1_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk1_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r3_waybel_9(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( ~ m1_subset_1(esk11_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_43]),c_0_44])]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_82,plain,
    ( m1_subset_1(esk11_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_83,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v4_orders_2(X15)
      | ~ v7_waybel_0(X15)
      | ~ l1_waybel_0(X15,X14)
      | m1_subset_1(k10_yellow_6(X14,X15),k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_84,negated_conjecture,
    ( r3_waybel_9(esk1_0,X1,X2)
    | v1_compts_1(esk1_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,esk3_1(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_85,plain,
    ( r3_waybel_9(X1,X2,esk8_1(k10_yellow_6(X1,X2)))
    | v1_xboole_0(k10_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(esk8_1(k10_yellow_6(X1,X2)),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_25])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_43]),c_0_44])]),c_0_45]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk12_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( r3_waybel_9(esk1_0,X1,esk8_1(k10_yellow_6(esk1_0,esk3_1(X1))))
    | v1_xboole_0(k10_yellow_6(esk1_0,esk3_1(X1)))
    | v2_struct_0(esk3_1(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk8_1(k10_yellow_6(esk1_0,esk3_1(X1))),u1_struct_0(esk1_0))
    | ~ l1_waybel_0(esk3_1(X1),esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(esk3_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk3_1(X1))
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_43]),c_0_44])]),c_0_45]),c_0_86])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k10_yellow_6(X2,X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(k10_yellow_6(esk1_0,esk3_1(esk12_1(esk1_0))))
    | v2_struct_0(esk3_1(esk12_1(esk1_0)))
    | v2_struct_0(esk12_1(esk1_0))
    | ~ m1_subset_1(esk8_1(k10_yellow_6(esk1_0,esk3_1(esk12_1(esk1_0)))),u1_struct_0(esk1_0))
    | ~ l1_waybel_0(esk3_1(esk12_1(esk1_0)),esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk3_1(esk12_1(esk1_0)))
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk3_1(esk12_1(esk1_0)))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_43]),c_0_44])]),c_0_86]),c_0_45])).

cnf(c_0_92,plain,
    ( v1_xboole_0(k10_yellow_6(X1,X2))
    | m1_subset_1(esk8_1(k10_yellow_6(X1,X2)),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_25])).

cnf(c_0_93,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_94,negated_conjecture,
    ( v3_yellow_6(esk3_1(X1),esk1_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk1_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(k10_yellow_6(esk1_0,esk3_1(esk12_1(esk1_0))))
    | v2_struct_0(esk3_1(esk12_1(esk1_0)))
    | v2_struct_0(esk12_1(esk1_0))
    | ~ l1_waybel_0(esk3_1(esk12_1(esk1_0)),esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk3_1(esk12_1(esk1_0)))
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk3_1(esk12_1(esk1_0)))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_96,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk3_1(X1))
    | v2_struct_0(X1)
    | k10_yellow_6(esk1_0,esk3_1(X1)) != k1_xboole_0
    | ~ l1_waybel_0(esk3_1(X1),esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(esk3_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk3_1(X1))
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_97,negated_conjecture,
    ( k10_yellow_6(esk1_0,esk3_1(esk12_1(esk1_0))) = k1_xboole_0
    | v2_struct_0(esk3_1(esk12_1(esk1_0)))
    | v2_struct_0(esk12_1(esk1_0))
    | ~ l1_waybel_0(esk3_1(esk12_1(esk1_0)),esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk3_1(esk12_1(esk1_0)))
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk3_1(esk12_1(esk1_0)))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( v2_struct_0(esk3_1(esk12_1(esk1_0)))
    | v2_struct_0(esk12_1(esk1_0))
    | ~ l1_waybel_0(esk3_1(esk12_1(esk1_0)),esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk3_1(esk12_1(esk1_0)))
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk3_1(esk12_1(esk1_0)))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_86])).

cnf(c_0_99,negated_conjecture,
    ( v7_waybel_0(esk3_1(X1))
    | v1_compts_1(esk1_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_79]),c_0_45])).

cnf(c_0_100,negated_conjecture,
    ( v2_struct_0(esk3_1(esk12_1(esk1_0)))
    | v2_struct_0(esk12_1(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(esk3_1(esk12_1(esk1_0)),esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk3_1(esk12_1(esk1_0)))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_86])).

cnf(c_0_101,negated_conjecture,
    ( v4_orders_2(esk3_1(X1))
    | v1_compts_1(esk1_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_45])).

cnf(c_0_102,negated_conjecture,
    ( v2_struct_0(esk3_1(esk12_1(esk1_0)))
    | v2_struct_0(esk12_1(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(esk3_1(esk12_1(esk1_0)),esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( l1_waybel_0(esk3_1(X1),esk1_0)
    | v1_compts_1(esk1_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_79]),c_0_45])).

cnf(c_0_104,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk3_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_79]),c_0_45])).

cnf(c_0_105,negated_conjecture,
    ( v2_struct_0(esk3_1(esk12_1(esk1_0)))
    | v2_struct_0(esk12_1(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_86])).

cnf(c_0_106,negated_conjecture,
    ( v2_struct_0(esk12_1(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v7_waybel_0(esk12_1(esk1_0))
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_86])).

cnf(c_0_107,plain,
    ( v7_waybel_0(esk12_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_108,negated_conjecture,
    ( v2_struct_0(esk12_1(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0)
    | ~ v4_orders_2(esk12_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_43]),c_0_44])]),c_0_86]),c_0_45])).

cnf(c_0_109,plain,
    ( v4_orders_2(esk12_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_110,negated_conjecture,
    ( v2_struct_0(esk12_1(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_waybel_0(esk12_1(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_43]),c_0_44])]),c_0_86]),c_0_45])).

cnf(c_0_111,plain,
    ( l1_waybel_0(esk12_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_112,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk12_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_113,negated_conjecture,
    ( v2_struct_0(esk12_1(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_43]),c_0_44])]),c_0_86]),c_0_45])).

cnf(c_0_114,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_43]),c_0_44])]),c_0_86]),c_0_45])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_61]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
