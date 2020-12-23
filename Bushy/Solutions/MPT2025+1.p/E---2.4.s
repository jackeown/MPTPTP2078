%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t24_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 190.73s
% Output     : CNFRefutation 190.73s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 523 expanded)
%              Number of clauses        :   65 ( 182 expanded)
%              Number of leaves         :   18 ( 129 expanded)
%              Depth                    :   10
%              Number of atoms          :  593 (4502 expanded)
%              Number of equality atoms :   43 ( 364 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   81 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',d18_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',dt_k10_yellow_6)).

fof(t24_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v4_orders_2(X3)
                & v7_waybel_0(X3)
                & l1_waybel_0(X3,X1) )
             => ( r2_hidden(X2,k10_yellow_6(X1,X3))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = k2_relset_1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3))
                     => r2_hidden(X2,k2_pre_topc(X1,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t24_waybel_9)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t55_tops_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',existence_m1_subset_1)).

fof(d13_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k2_pre_topc(X1,X2)
              <=> ! [X4] :
                    ( r2_hidden(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X5,X1)
                              & r2_hidden(X4,X5)
                              & r1_xboole_0(X2,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',d13_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',dt_k2_pre_topc)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t2_subset)).

fof(t26_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ~ ( r1_waybel_0(X1,X2,X3)
                & r1_waybel_0(X1,X2,X4)
                & r1_xboole_0(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t26_yellow_6)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t1_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',d1_connsp_2)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',dt_k1_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',projectivity_k1_tops_1)).

fof(t8_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t8_waybel_9)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t7_boole)).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X24,X25,X29] :
      ( ( ~ r2_hidden(X24,X23)
        | ~ m1_connsp_2(X25,X21,X24)
        | r1_waybel_0(X21,X22,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | X23 != k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_connsp_2(esk8_4(X21,X22,X23,X24),X21,X24)
        | r2_hidden(X24,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | X23 != k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_waybel_0(X21,X22,esk8_4(X21,X22,X23,X24))
        | r2_hidden(X24,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | X23 != k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk9_3(X21,X22,X23),u1_struct_0(X21))
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_connsp_2(esk10_3(X21,X22,X23),X21,esk9_3(X21,X22,X23))
        | ~ r2_hidden(esk9_3(X21,X22,X23),X23)
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_waybel_0(X21,X22,esk10_3(X21,X22,X23))
        | ~ r2_hidden(esk9_3(X21,X22,X23),X23)
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk9_3(X21,X22,X23),X23)
        | ~ m1_connsp_2(X29,X21,esk9_3(X21,X22,X23))
        | r1_waybel_0(X21,X22,X29)
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_19,plain,(
    ! [X80,X81,X82] :
      ( ~ r2_hidden(X80,X81)
      | ~ m1_subset_1(X81,k1_zfmisc_1(X82))
      | m1_subset_1(X80,X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ v4_orders_2(X34)
      | ~ v7_waybel_0(X34)
      | ~ l1_waybel_0(X34,X33)
      | m1_subset_1(k10_yellow_6(X33,X34),k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v4_orders_2(X3)
                  & v7_waybel_0(X3)
                  & l1_waybel_0(X3,X1) )
               => ( r2_hidden(X2,k10_yellow_6(X1,X3))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X4 = k2_relset_1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3))
                       => r2_hidden(X2,k2_pre_topc(X1,X4)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_waybel_9])).

fof(c_0_22,plain,(
    ! [X83,X84,X85,X86] :
      ( ( ~ v3_pre_topc(X86,X84)
        | k1_tops_1(X84,X86) = X86
        | ~ m1_subset_1(X86,k1_zfmisc_1(u1_struct_0(X84)))
        | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X83)))
        | ~ l1_pre_topc(X84)
        | ~ v2_pre_topc(X83)
        | ~ l1_pre_topc(X83) )
      & ( k1_tops_1(X83,X85) != X85
        | v3_pre_topc(X85,X83)
        | ~ m1_subset_1(X86,k1_zfmisc_1(u1_struct_0(X84)))
        | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(X83)))
        | ~ l1_pre_topc(X84)
        | ~ v2_pre_topc(X83)
        | ~ l1_pre_topc(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

fof(c_0_23,plain,(
    ! [X59] : m1_subset_1(esk16_1(X59),X59) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_24,plain,(
    ! [X12,X13,X14,X15,X16,X20] :
      ( ( ~ r2_hidden(X15,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v3_pre_topc(X16,X12)
        | ~ r2_hidden(X15,X16)
        | ~ r1_xboole_0(X13,X16)
        | ~ r2_hidden(X15,u1_struct_0(X12))
        | X14 != k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk5_4(X12,X13,X14,X15),k1_zfmisc_1(u1_struct_0(X12)))
        | r2_hidden(X15,X14)
        | ~ r2_hidden(X15,u1_struct_0(X12))
        | X14 != k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(esk5_4(X12,X13,X14,X15),X12)
        | r2_hidden(X15,X14)
        | ~ r2_hidden(X15,u1_struct_0(X12))
        | X14 != k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(X15,esk5_4(X12,X13,X14,X15))
        | r2_hidden(X15,X14)
        | ~ r2_hidden(X15,u1_struct_0(X12))
        | X14 != k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r1_xboole_0(X13,esk5_4(X12,X13,X14,X15))
        | r2_hidden(X15,X14)
        | ~ r2_hidden(X15,u1_struct_0(X12))
        | X14 != k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk6_3(X12,X13,X14),u1_struct_0(X12))
        | X14 = k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk7_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(esk6_3(X12,X13,X14),X14)
        | X14 = k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(esk7_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk6_3(X12,X13,X14),X14)
        | X14 = k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk6_3(X12,X13,X14),esk7_3(X12,X13,X14))
        | ~ r2_hidden(esk6_3(X12,X13,X14),X14)
        | X14 = k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r1_xboole_0(X13,esk7_3(X12,X13,X14))
        | ~ r2_hidden(esk6_3(X12,X13,X14),X14)
        | X14 = k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk6_3(X12,X13,X14),X14)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v3_pre_topc(X20,X12)
        | ~ r2_hidden(esk6_3(X12,X13,X14),X20)
        | ~ r1_xboole_0(X13,X20)
        | X14 = k2_pre_topc(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

fof(c_0_25,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | m1_subset_1(k2_pre_topc(X37,X38),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_26,plain,(
    ! [X87,X88,X89] :
      ( ~ r2_hidden(X87,X88)
      | ~ m1_subset_1(X88,k1_zfmisc_1(X89))
      | ~ v1_xboole_0(X89) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_27,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ v2_struct_0(esk3_0)
    & v4_orders_2(esk3_0)
    & v7_waybel_0(esk3_0)
    & l1_waybel_0(esk3_0,esk1_0)
    & r2_hidden(esk2_0,k10_yellow_6(esk1_0,esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & esk4_0 = k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_waybel_0(esk1_0,esk3_0))
    & ~ r2_hidden(esk2_0,k2_pre_topc(esk1_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_31,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk16_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v3_pre_topc(esk5_4(X1,X2,X3,X4),X1)
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X76,X77] :
      ( ~ m1_subset_1(X76,X77)
      | v1_xboole_0(X77)
      | r2_hidden(X76,X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,esk5_4(X2,X3,X4,X1))
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | X4 != k2_pre_topc(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_39,plain,(
    ! [X72,X73,X74,X75] :
      ( v2_struct_0(X72)
      | ~ l1_struct_0(X72)
      | v2_struct_0(X73)
      | ~ v4_orders_2(X73)
      | ~ v7_waybel_0(X73)
      | ~ l1_waybel_0(X73,X72)
      | ~ r1_waybel_0(X72,X73,X74)
      | ~ r1_waybel_0(X72,X73,X75)
      | ~ r1_xboole_0(X74,X75) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow_6])])])])).

cnf(c_0_40,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_27,c_0_28])]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_0,k10_yellow_6(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | m1_subset_1(esk5_4(X2,X3,k2_pre_topc(X2,X3),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_51,plain,
    ( v3_pre_topc(esk5_4(X1,X2,k2_pre_topc(X1,X2),X3),X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_34])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

fof(c_0_55,plain,(
    ! [X70,X71] :
      ( ~ r2_hidden(X70,X71)
      | m1_subset_1(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,esk5_4(X2,X3,k2_pre_topc(X2,X3),X1))
    | r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_waybel_0(X1,X2,X4)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk3_0,X1)
    | ~ m1_connsp_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])]),c_0_47]),c_0_48])).

fof(c_0_60,plain,(
    ! [X43] :
      ( ~ l1_pre_topc(X43)
      | l1_struct_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_61,plain,(
    ! [X30,X31,X32] :
      ( ( ~ m1_connsp_2(X32,X30,X31)
        | r2_hidden(X31,k1_tops_1(X30,X32))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r2_hidden(X31,k1_tops_1(X30,X32))
        | m1_connsp_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_62,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | m1_subset_1(k1_tops_1(X35,X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_63,plain,(
    ! [X61,X62] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | k1_tops_1(X61,k1_tops_1(X61,X62)) = k1_tops_1(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_64,plain,
    ( k1_tops_1(X1,esk5_4(X1,X2,k2_pre_topc(X1,X2),X3)) = esk5_4(X1,X2,k2_pre_topc(X1,X2),X3)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])]),c_0_47]),c_0_48])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),X1))
    | r2_hidden(X1,k2_pre_topc(esk1_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_45])])).

cnf(c_0_69,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ r1_waybel_0(esk1_0,esk3_0,X1)
    | ~ m1_connsp_2(X2,esk1_0,esk2_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_42]),c_0_43]),c_0_44])]),c_0_48]),c_0_47])).

cnf(c_0_70,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_71,plain,(
    ! [X95,X96] :
      ( v2_struct_0(X95)
      | ~ l1_struct_0(X95)
      | v2_struct_0(X96)
      | ~ l1_waybel_0(X96,X95)
      | r1_waybel_0(X95,X96,k2_relset_1(u1_struct_0(X96),u1_struct_0(X95),u1_waybel_0(X95,X96))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_9])])])])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,esk5_4(X2,X1,X3,X4))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X2))
    | X3 != k2_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_73,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( k1_tops_1(esk1_0,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),X1)) = esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),X1)
    | r2_hidden(X1,k2_pre_topc(esk1_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_57]),c_0_45])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k2_pre_topc(esk1_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_79,plain,(
    ! [X91,X92] :
      ( ~ r2_hidden(X91,X92)
      | ~ v1_xboole_0(X92) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk1_0,esk4_0))
    | m1_subset_1(X1,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),X1))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk3_0,X1)
    | ~ m1_connsp_2(X2,esk1_0,esk2_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_45])])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_waybel_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_84,plain,
    ( r1_xboole_0(X1,esk5_4(X2,X1,k2_pre_topc(X2,X1),X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_72]),c_0_34])).

cnf(c_0_85,plain,
    ( m1_connsp_2(k1_tops_1(X1,X2),X1,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k1_tops_1(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,esk5_4(X1,X2,k2_pre_topc(X1,X2),X3))) = k1_tops_1(X1,esk5_4(X1,X2,k2_pre_topc(X1,X2),X3))
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_50])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( k1_tops_1(esk1_0,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0)) = esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk2_0,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_77]),c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ m1_connsp_2(X1,esk1_0,esk2_0)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_42])]),c_0_48]),c_0_47])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),X1))
    | r2_hidden(X1,k2_pre_topc(esk1_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_57]),c_0_45])])).

cnf(c_0_93,plain,
    ( m1_connsp_2(k1_tops_1(X1,esk5_4(X1,X2,k2_pre_topc(X1,X2),X3)),X1,X4)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ r2_hidden(X4,k1_tops_1(X1,esk5_4(X1,X2,k2_pre_topc(X1,X2),X3)))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_50])).

cnf(c_0_94,negated_conjecture,
    ( k1_tops_1(esk1_0,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0)) = esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_45]),c_0_46])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk1_0,esk4_0))
    | ~ v1_xboole_0(esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),X1))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_68])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0))
    | r2_hidden(esk2_0,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk1_0,esk4_0))
    | ~ l1_struct_0(esk1_0)
    | ~ m1_connsp_2(esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),X1),esk1_0,esk2_0)
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0),esk1_0,X1)
    | ~ r2_hidden(X1,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_77]),c_0_57]),c_0_45]),c_0_46])]),c_0_78]),c_0_47])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_4(esk1_0,esk4_0,k2_pre_topc(esk1_0,esk4_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_77])]),c_0_78])).

cnf(c_0_100,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_77]),c_0_99])]),c_0_78])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_70]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
