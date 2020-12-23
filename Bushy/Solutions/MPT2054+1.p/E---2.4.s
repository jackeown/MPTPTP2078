%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t13_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:49 EDT 2019

% Result     : Theorem 245.24s
% Output     : CNFRefutation 245.24s
% Verified   : 
% Statistics : Number of formulae       :  122 (1703 expanded)
%              Number of clauses        :   89 ( 620 expanded)
%              Number of leaves         :   16 ( 402 expanded)
%              Depth                    :   16
%              Number of atoms          :  671 (13739 expanded)
%              Number of equality atoms :   20 ( 135 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   81 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_yellow19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',t13_yellow19)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',t4_subset)).

fof(d5_waybel_7,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( r2_waybel_7(X1,X2,X3)
        <=> ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X4,X1)
                  & r2_hidden(X3,X4) )
               => r2_hidden(X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',d5_waybel_7)).

fof(d18_yellow_6,axiom,(
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
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k10_yellow_6(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_connsp_2(X5,X1,X4)
                         => r1_waybel_0(X1,X2,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',d18_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',dt_k10_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',dt_l1_pre_topc)).

fof(d3_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => k2_yellow19(X1,X2) = a_2_1_yellow19(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',d3_yellow19)).

fof(t11_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_hidden(X3,k2_yellow19(X1,X2))
            <=> ( r1_waybel_0(X1,X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',t11_yellow19)).

fof(fraenkel_a_2_1_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X2) )
     => ( r2_hidden(X1,a_2_1_yellow19(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = X4
            & r1_waybel_0(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',fraenkel_a_2_1_yellow19)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',dt_m1_connsp_2)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',d1_connsp_2)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',fc9_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',dt_k1_tops_1)).

fof(t8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( r1_tarski(X3,X4)
             => ( ( r1_waybel_0(X1,X2,X3)
                 => r1_waybel_0(X1,X2,X4) )
                & ( r2_waybel_0(X1,X2,X3)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',t8_waybel_0)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t13_yellow19.p',t44_tops_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t13_yellow19])).

fof(c_0_17,plain,(
    ! [X89,X90,X91] :
      ( v2_struct_0(X89)
      | ~ v2_pre_topc(X89)
      | ~ l1_pre_topc(X89)
      | ~ m1_subset_1(X90,k1_zfmisc_1(u1_struct_0(X89)))
      | ~ m1_subset_1(X91,u1_struct_0(X89))
      | ~ v3_pre_topc(X90,X89)
      | ~ r2_hidden(X91,X90)
      | m1_connsp_2(X90,X89,X91) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_18,plain,(
    ! [X86,X87,X88] :
      ( ~ r2_hidden(X86,X87)
      | ~ m1_subset_1(X87,k1_zfmisc_1(X88))
      | m1_subset_1(X86,X88) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_19,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_waybel_7(X26,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v3_pre_topc(X29,X26)
        | ~ r2_hidden(X28,X29)
        | r2_hidden(X29,X27)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk7_3(X26,X30,X31),k1_zfmisc_1(u1_struct_0(X26)))
        | r2_waybel_7(X26,X30,X31)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v3_pre_topc(esk7_3(X26,X30,X31),X26)
        | r2_waybel_7(X26,X30,X31)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(X31,esk7_3(X26,X30,X31))
        | r2_waybel_7(X26,X30,X31)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r2_hidden(esk7_3(X26,X30,X31),X30)
        | r2_waybel_7(X26,X30,X31)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & v7_waybel_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
      | ~ r2_waybel_7(esk1_0,k2_yellow19(esk1_0,esk2_0),esk3_0) )
    & ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
      | r2_waybel_7(esk1_0,k2_yellow19(esk1_0,esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X12,X13,X14,X15,X16,X20] :
      ( ( ~ r2_hidden(X15,X14)
        | ~ m1_connsp_2(X16,X12,X15)
        | r1_waybel_0(X12,X13,X16)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | X14 != k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_connsp_2(esk4_4(X12,X13,X14,X15),X12,X15)
        | r2_hidden(X15,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | X14 != k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r1_waybel_0(X12,X13,esk4_4(X12,X13,X14,X15))
        | r2_hidden(X15,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | X14 != k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk5_3(X12,X13,X14),u1_struct_0(X12))
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_connsp_2(esk6_3(X12,X13,X14),X12,esk5_3(X12,X13,X14))
        | ~ r2_hidden(esk5_3(X12,X13,X14),X14)
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r1_waybel_0(X12,X13,esk6_3(X12,X13,X14))
        | ~ r2_hidden(esk5_3(X12,X13,X14),X14)
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk5_3(X12,X13,X14),X14)
        | ~ m1_connsp_2(X20,X12,esk5_3(X12,X13,X14))
        | r1_waybel_0(X12,X13,X20)
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ v4_orders_2(X36)
      | ~ v7_waybel_0(X36)
      | ~ l1_waybel_0(X36,X35)
      | m1_subset_1(k10_yellow_6(X35,X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | l1_struct_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_26,plain,
    ( r2_hidden(X4,X2)
    | ~ r2_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v3_pre_topc(esk7_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r1_waybel_0(X4,X5,X3)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_connsp_2(X3,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | X2 != k10_yellow_6(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v4_orders_2(X5)
    | ~ v7_waybel_0(X5)
    | ~ l1_waybel_0(X5,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | v2_struct_0(X25)
      | ~ l1_waybel_0(X25,X24)
      | k2_yellow19(X24,X25) = a_2_1_yellow19(X24,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_yellow19])])])])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X72,X73,X74] :
      ( ( r1_waybel_0(X72,X73,X74)
        | ~ r2_hidden(X74,k2_yellow19(X72,X73))
        | v2_struct_0(X73)
        | ~ l1_waybel_0(X73,X72)
        | v2_struct_0(X72)
        | ~ l1_struct_0(X72) )
      & ( m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X72)))
        | ~ r2_hidden(X74,k2_yellow19(X72,X73))
        | v2_struct_0(X73)
        | ~ l1_waybel_0(X73,X72)
        | v2_struct_0(X72)
        | ~ l1_struct_0(X72) )
      & ( ~ r1_waybel_0(X72,X73,X74)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X72)))
        | r2_hidden(X74,k2_yellow19(X72,X73))
        | v2_struct_0(X73)
        | ~ l1_waybel_0(X73,X72)
        | v2_struct_0(X72)
        | ~ l1_struct_0(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t11_yellow19])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r2_waybel_7(esk1_0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( v3_pre_topc(esk7_3(esk1_0,X1,X2),esk1_0)
    | r2_waybel_7(esk1_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_7(esk1_0,X1,X2)
    | m1_subset_1(esk7_3(esk1_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_28])])).

cnf(c_0_41,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_24])]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( m1_connsp_2(X1,esk1_0,X2)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_28])]),c_0_34])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,esk7_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( m1_connsp_2(esk4_4(X1,X2,X3,X4),X1,X4)
    | r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_48,plain,(
    ! [X61,X62,X63,X65] :
      ( ( m1_subset_1(esk14_3(X61,X62,X63),k1_zfmisc_1(u1_struct_0(X62)))
        | ~ r2_hidden(X61,a_2_1_yellow19(X62,X63))
        | v2_struct_0(X62)
        | ~ l1_struct_0(X62)
        | v2_struct_0(X63)
        | ~ l1_waybel_0(X63,X62) )
      & ( X61 = esk14_3(X61,X62,X63)
        | ~ r2_hidden(X61,a_2_1_yellow19(X62,X63))
        | v2_struct_0(X62)
        | ~ l1_struct_0(X62)
        | v2_struct_0(X63)
        | ~ l1_waybel_0(X63,X62) )
      & ( r1_waybel_0(X62,X63,esk14_3(X61,X62,X63))
        | ~ r2_hidden(X61,a_2_1_yellow19(X62,X63))
        | v2_struct_0(X62)
        | ~ l1_struct_0(X62)
        | v2_struct_0(X63)
        | ~ l1_waybel_0(X63,X62) )
      & ( ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X62)))
        | X61 != X65
        | ~ r1_waybel_0(X62,X63,X65)
        | r2_hidden(X61,a_2_1_yellow19(X62,X63))
        | v2_struct_0(X62)
        | ~ l1_struct_0(X62)
        | v2_struct_0(X63)
        | ~ l1_waybel_0(X63,X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_yellow19])])])])])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_yellow19(X1,X2) = a_2_1_yellow19(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_51,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( r2_waybel_7(esk1_0,X1,X2)
    | r2_hidden(esk7_3(esk1_0,X1,X2),X3)
    | ~ r2_waybel_7(esk1_0,X3,X4)
    | ~ r2_hidden(X4,esk7_3(esk1_0,X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    | r2_waybel_7(esk1_0,k2_yellow19(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( r1_waybel_0(X1,esk2_0,X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X2,X1,X3)
    | ~ r2_hidden(X3,k10_yellow_6(X1,esk2_0))
    | ~ l1_waybel_0(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( m1_connsp_2(esk7_3(esk1_0,X1,X2),esk1_0,X3)
    | r2_waybel_7(esk1_0,X1,X2)
    | ~ r2_hidden(X3,esk7_3(esk1_0,X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( r2_waybel_7(esk1_0,X1,X2)
    | r2_hidden(X2,esk7_3(esk1_0,X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_28])])).

fof(c_0_58,plain,(
    ! [X47,X48,X49] :
      ( v2_struct_0(X47)
      | ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | ~ m1_connsp_2(X49,X47,X48)
      | m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_59,plain,
    ( m1_connsp_2(esk4_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_32])).

cnf(c_0_60,plain,
    ( r2_hidden(X3,a_2_1_yellow19(X2,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X1
    | ~ r1_waybel_0(X2,X4,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( a_2_1_yellow19(esk1_0,X1) = k2_yellow19(esk1_0,X1)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_0(esk1_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k2_yellow19(esk1_0,X1))
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_50]),c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( r2_waybel_7(esk1_0,X1,X2)
    | r2_hidden(esk7_3(esk1_0,X1,X2),k2_yellow19(esk1_0,esk2_0))
    | r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    | ~ r2_hidden(esk3_0,esk7_3(esk1_0,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ m1_connsp_2(X1,esk1_0,X2)
    | ~ r2_hidden(X2,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_55]),c_0_28])]),c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( m1_connsp_2(esk7_3(esk1_0,X1,X2),esk1_0,X2)
    | r2_waybel_7(esk1_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( m1_connsp_2(esk4_4(X1,esk2_0,k10_yellow_6(X1,esk2_0),X2),X1,X2)
    | r2_hidden(X2,k10_yellow_6(X1,esk2_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ r1_waybel_0(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_waybel_0(X3,X2) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( a_2_1_yellow19(esk1_0,esk2_0) = k2_yellow19(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_55]),c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ r2_hidden(X1,k2_yellow19(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_55]),c_0_44])).

cnf(c_0_71,negated_conjecture,
    ( r2_waybel_7(esk1_0,X1,esk3_0)
    | r2_hidden(esk7_3(esk1_0,X1,esk3_0),k2_yellow19(esk1_0,esk2_0))
    | r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk7_3(esk1_0,X1,X2))
    | r2_waybel_7(esk1_0,X1,X2)
    | ~ r2_hidden(X2,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_73,plain,(
    ! [X21,X22,X23] :
      ( ( ~ m1_connsp_2(X23,X21,X22)
        | r2_hidden(X22,k1_tops_1(X21,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(X22,k1_tops_1(X21,X23))
        | m1_connsp_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_74,plain,(
    ! [X104,X105] :
      ( ~ v2_pre_topc(X104)
      | ~ l1_pre_topc(X104)
      | ~ m1_subset_1(X105,k1_zfmisc_1(u1_struct_0(X104)))
      | v3_pre_topc(k1_tops_1(X104,X105),X104) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_connsp_2(X1,esk1_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_27]),c_0_28])]),c_0_34])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_77,negated_conjecture,
    ( m1_connsp_2(esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),X1),esk1_0,X1)
    | r2_hidden(X1,k10_yellow_6(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_27]),c_0_55]),c_0_28])]),c_0_34])).

cnf(c_0_78,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(X1,k2_yellow19(esk1_0,esk2_0))
    | ~ r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_50]),c_0_55])]),c_0_34]),c_0_44])).

cnf(c_0_80,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk7_3(esk1_0,X1,esk3_0))
    | r2_waybel_7(esk1_0,X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

fof(c_0_81,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | m1_subset_1(k1_tops_1(X37,X38),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_82,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_connsp_2(X1,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( m1_connsp_2(esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0),esk1_0,esk3_0)
    | r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( r2_waybel_7(esk1_0,X1,X2)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_27]),c_0_28])])).

cnf(c_0_87,negated_conjecture,
    ( r2_waybel_7(esk1_0,X1,esk3_0)
    | r2_hidden(esk7_3(esk1_0,X1,esk3_0),k2_yellow19(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_40])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_82,c_0_66])).

cnf(c_0_90,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_27]),c_0_28])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    | m1_subset_1(esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    | ~ r2_waybel_7(esk1_0,k2_yellow19(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_94,negated_conjecture,
    ( r2_waybel_7(esk1_0,k2_yellow19(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_27])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,X2))
    | ~ m1_connsp_2(X2,esk1_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_27]),c_0_28])]),c_0_34])).

fof(c_0_97,plain,(
    ! [X100,X101,X102,X103] :
      ( ( ~ r1_waybel_0(X100,X101,X102)
        | r1_waybel_0(X100,X101,X103)
        | ~ r1_tarski(X102,X103)
        | v2_struct_0(X101)
        | ~ l1_waybel_0(X101,X100)
        | v2_struct_0(X100)
        | ~ l1_struct_0(X100) )
      & ( ~ r2_waybel_0(X100,X101,X102)
        | r2_waybel_0(X100,X101,X103)
        | ~ r1_tarski(X102,X103)
        | v2_struct_0(X101)
        | ~ l1_waybel_0(X101,X100)
        | v2_struct_0(X100)
        | ~ l1_struct_0(X100) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).

fof(c_0_98,plain,(
    ! [X84,X85] :
      ( ~ l1_pre_topc(X84)
      | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X84)))
      | r1_tarski(k1_tops_1(X84,X85),X85) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_99,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X2,X3,esk4_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_90]),c_0_32])).

cnf(c_0_100,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)),esk1_0)
    | r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    | m1_subset_1(k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk1_0,X1))
    | ~ m1_connsp_2(X1,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_76])).

cnf(c_0_104,plain,
    ( r1_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_tarski(X3,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_105,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(X2,esk2_0))
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X2,esk2_0,esk4_4(X2,esk2_0,k10_yellow_6(X2,esk2_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_waybel_0(esk2_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_107,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)),esk1_0) ),
    inference(sr,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[c_0_102,c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)))
    | r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_85])).

cnf(c_0_110,negated_conjecture,
    ( r1_waybel_0(esk1_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r1_tarski(X3,X2)
    | ~ r1_waybel_0(esk1_0,X1,X3)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_50]),c_0_34])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_27])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk1_0,esk2_0))
    | ~ r1_waybel_0(esk1_0,esk2_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_27]),c_0_55]),c_0_28])]),c_0_34])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)),X1)
    | ~ r2_waybel_7(esk1_0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_107]),c_0_108])])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0))) ),
    inference(sr,[status(thm)],[c_0_109,c_0_101])).

cnf(c_0_115,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_waybel_0(esk1_0,esk2_0,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_55]),c_0_44])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)),esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0))
    | r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_92])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    | ~ r1_waybel_0(esk1_0,esk2_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_76])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0)),k2_yellow19(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_94]),c_0_114])])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    | ~ r1_waybel_0(esk1_0,esk2_0,k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,k1_tops_1(esk1_0,esk4_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120])]),c_0_101]),
    [proof]).
%------------------------------------------------------------------------------
