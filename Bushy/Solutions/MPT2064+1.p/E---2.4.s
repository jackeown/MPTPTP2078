%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t24_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 279.90s
% Output     : CNFRefutation 279.90s
% Verified   : 
% Statistics : Number of formulae       :  163 (15512 expanded)
%              Number of clauses        :  132 (5358 expanded)
%              Number of leaves         :   16 (4008 expanded)
%              Depth                    :   24
%              Number of atoms          :  959 (183239 expanded)
%              Number of equality atoms :   11 ( 218 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   54 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_yellow19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t24_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t32_waybel_9)).

fof(t21_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2,X3] :
          ( ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) )
         => ( r1_waybel_0(X1,X3,X2)
           => ! [X4] :
                ( m2_yellow_6(X4,X1,X3)
               => r1_waybel_0(X1,X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t21_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',dt_m2_yellow_6)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t7_boole)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',d19_yellow_6)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',d2_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t29_waybel_9)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t4_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',dt_k2_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t23_yellow19)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t1_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t24_yellow19.p',t6_boole)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t24_yellow19])).

fof(c_0_17,negated_conjecture,(
    ! [X8] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
      & ( ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ v3_yellow_6(X8,esk1_0)
        | ~ l1_waybel_0(X8,esk1_0)
        | ~ r1_waybel_0(esk1_0,X8,esk2_0)
        | ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,X8)) )
      & ( ~ v2_struct_0(esk4_0)
        | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( v4_orders_2(esk4_0)
        | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( v7_waybel_0(esk4_0)
        | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( v3_yellow_6(esk4_0,esk1_0)
        | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( l1_waybel_0(esk4_0,esk1_0)
        | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
        | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) )
      & ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk4_0))
        | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

fof(c_0_18,plain,(
    ! [X53,X54,X55] :
      ( ( m2_yellow_6(esk12_3(X53,X54,X55),X53,X54)
        | ~ r3_waybel_9(X53,X54,X55)
        | ~ m1_subset_1(X55,u1_struct_0(X53))
        | v2_struct_0(X54)
        | ~ v4_orders_2(X54)
        | ~ v7_waybel_0(X54)
        | ~ l1_waybel_0(X54,X53)
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) )
      & ( r2_hidden(X55,k10_yellow_6(X53,esk12_3(X53,X54,X55)))
        | ~ r3_waybel_9(X53,X54,X55)
        | ~ m1_subset_1(X55,u1_struct_0(X53))
        | v2_struct_0(X54)
        | ~ v4_orders_2(X54)
        | ~ v7_waybel_0(X54)
        | ~ l1_waybel_0(X54,X53)
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

fof(c_0_19,plain,(
    ! [X39,X40,X41,X42] :
      ( v2_struct_0(X39)
      | ~ l1_struct_0(X39)
      | v2_struct_0(X41)
      | ~ v4_orders_2(X41)
      | ~ v7_waybel_0(X41)
      | ~ l1_waybel_0(X41,X39)
      | ~ r1_waybel_0(X39,X41,X40)
      | ~ m2_yellow_6(X42,X39,X41)
      | r1_waybel_0(X39,X42,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_yellow19])])])])).

fof(c_0_20,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_21,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v3_yellow_6(X1,esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk12_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_waybel_0(X1,X4,X3)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ m2_yellow_6(X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m2_yellow_6(esk12_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_struct_0(X24)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) )
      & ( v4_orders_2(X24)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) )
      & ( v7_waybel_0(X24)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) )
      & ( l1_waybel_0(X24,X22)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

fof(c_0_31,plain,(
    ! [X66,X67] :
      ( ~ r2_hidden(X66,X67)
      | ~ v1_xboole_0(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_32,negated_conjecture,
    ( v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,esk12_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk12_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v3_yellow_6(esk12_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk12_3(esk1_0,X1,esk3_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_33,plain,
    ( r1_waybel_0(X1,esk12_3(X1,X2,X3),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ r1_waybel_0(X1,X2,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_38,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_39,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(esk12_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v3_yellow_6(esk12_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk12_3(esk1_0,X1,esk3_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_43,plain,
    ( l1_waybel_0(esk12_3(X1,X2,X3),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_29])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X1,X3)
    | ~ v1_xboole_0(k10_yellow_6(X2,esk12_3(X2,X1,X3)))
    | ~ l1_waybel_0(X1,X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_45,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( v4_orders_2(esk12_3(X1,X2,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_29])).

cnf(c_0_48,plain,
    ( v7_waybel_0(esk12_3(X1,X2,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X1,X3)
    | ~ l1_waybel_0(X1,X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_struct_0(esk12_3(X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v3_yellow_6(esk12_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk12_3(esk1_0,X1,esk3_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_51,plain,
    ( v3_yellow_6(esk12_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),c_0_47]),c_0_48]),c_0_43]),c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(esk12_3(esk1_0,X1,esk3_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_53,plain,(
    ! [X48,X49,X50] :
      ( v2_struct_0(X48)
      | ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | v2_struct_0(X49)
      | ~ v4_orders_2(X49)
      | ~ v7_waybel_0(X49)
      | ~ l1_waybel_0(X49,X48)
      | ~ m1_subset_1(X50,u1_struct_0(X48))
      | ~ r2_hidden(X50,k10_yellow_6(X48,X49))
      | r3_waybel_9(X48,X49,X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_55,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk4_0))
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_61,plain,(
    ! [X59,X60,X61] :
      ( ~ r2_hidden(X59,X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(X61))
      | m1_subset_1(X59,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_62,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | m1_subset_1(k2_pre_topc(X16,X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

fof(c_0_65,plain,(
    ! [X43,X44,X45,X47] :
      ( ( ~ v2_struct_0(esk11_3(X43,X44,X45))
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v4_orders_2(esk11_3(X43,X44,X45))
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v7_waybel_0(esk11_3(X43,X44,X45))
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( l1_waybel_0(esk11_3(X43,X44,X45),X43)
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r1_waybel_0(X43,esk11_3(X43,X44,X45),X44)
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r3_waybel_9(X43,esk11_3(X43,X44,X45),X45)
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v2_struct_0(X47)
        | ~ v4_orders_2(X47)
        | ~ v7_waybel_0(X47)
        | ~ l1_waybel_0(X47,X43)
        | ~ r1_waybel_0(X43,X47,X44)
        | ~ r3_waybel_9(X43,X47,X45)
        | r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_yellow19])])])])])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( r3_waybel_9(X1,esk11_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk11_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_58])).

cnf(c_0_74,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_75,negated_conjecture,
    ( v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_68]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_77,plain,
    ( r3_waybel_9(X1,esk11_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( r1_waybel_0(X1,esk11_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk11_3(X1,X3,X2)) ),
    inference(csr,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_81,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_72]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_82,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_73]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_83,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_74]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_75]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | v2_struct_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ r1_waybel_0(esk1_0,esk11_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_87,plain,
    ( r1_waybel_0(X1,esk11_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_78,c_0_70])).

cnf(c_0_88,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | ~ v2_struct_0(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_64]),c_0_80]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_89,plain,
    ( l1_waybel_0(esk11_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_90,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | v2_struct_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ r1_waybel_0(esk1_0,esk11_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_77]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_91,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | ~ v2_struct_0(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_59]),c_0_80]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_92,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | v2_struct_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ r1_waybel_0(esk1_0,esk11_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_77]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_93,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | ~ v2_struct_0(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_58]),c_0_80]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_94,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | v2_struct_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ r1_waybel_0(esk1_0,esk11_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_77]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_95,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | ~ v2_struct_0(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_57]),c_0_80]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_96,negated_conjecture,
    ( v2_struct_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ r1_waybel_0(esk1_0,esk11_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_77]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_97,negated_conjecture,
    ( ~ v2_struct_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_60]),c_0_80]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_98,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_85])).

cnf(c_0_99,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_64]),c_0_88])).

cnf(c_0_100,plain,
    ( l1_waybel_0(esk11_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_89,c_0_70])).

cnf(c_0_101,plain,
    ( v7_waybel_0(esk11_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_102,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_87]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_59]),c_0_91])).

cnf(c_0_103,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_87]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_58]),c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_87]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_57]),c_0_95])).

cnf(c_0_105,negated_conjecture,
    ( ~ l1_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_87]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_60]),c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_98]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_107,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_108,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_64])).

cnf(c_0_109,plain,
    ( v7_waybel_0(esk11_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_101,c_0_70])).

cnf(c_0_110,plain,
    ( v4_orders_2(esk11_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_111,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_100]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_59])).

cnf(c_0_112,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_100]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_58])).

cnf(c_0_113,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_100]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_57])).

cnf(c_0_114,negated_conjecture,
    ( ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_100]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_60])).

cnf(c_0_115,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | v2_struct_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ r1_waybel_0(esk1_0,esk11_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_77]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_116,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | ~ v2_struct_0(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_85]),c_0_80]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_117,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_107])).

cnf(c_0_118,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0)
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_64])).

cnf(c_0_119,plain,
    ( v4_orders_2(esk11_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_110,c_0_70])).

cnf(c_0_120,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0)
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_109]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_59])).

cnf(c_0_121,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_109]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_58])).

cnf(c_0_122,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_109]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_57])).

cnf(c_0_123,negated_conjecture,
    ( ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_109]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_60])).

cnf(c_0_124,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_87]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_85]),c_0_116])).

cnf(c_0_125,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_117]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_126,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X51,X52)
      | v1_xboole_0(X52)
      | r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_127,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | m1_subset_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_128,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_129,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_64])).

cnf(c_0_130,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_119]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_59])).

cnf(c_0_131,negated_conjecture,
    ( v7_waybel_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_119]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_58])).

cnf(c_0_132,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_119]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_57])).

cnf(c_0_133,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_119]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_60])).

cnf(c_0_134,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_100]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_85])).

cnf(c_0_135,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | v2_struct_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ r1_waybel_0(esk1_0,esk11_3(esk1_0,X1,esk3_0),esk2_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,X1,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_77]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_136,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | ~ v2_struct_0(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_107]),c_0_80]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_137,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_138,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ r1_waybel_0(esk1_0,esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130]),c_0_131]),c_0_132]),c_0_23]),c_0_24]),c_0_25])]),c_0_133]),c_0_26])).

cnf(c_0_140,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0)
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_109]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_85])).

cnf(c_0_141,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | ~ l1_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_87]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_107]),c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( v1_xboole_0(k10_yellow_6(esk1_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v3_yellow_6(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(esk3_0,k10_yellow_6(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_pre_topc(esk1_0,X1))
    | ~ r1_waybel_0(esk1_0,esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_144,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_119]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_85])).

cnf(c_0_145,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk1_0,X1))
    | ~ r1_waybel_0(esk1_0,esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_139])).

cnf(c_0_146,negated_conjecture,
    ( r2_hidden(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | m1_subset_1(esk3_0,k10_yellow_6(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_56])).

cnf(c_0_147,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | ~ v7_waybel_0(esk11_3(esk1_0,esk2_0,esk3_0))
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_100]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_107])).

cnf(c_0_148,negated_conjecture,
    ( v1_xboole_0(k2_pre_topc(esk1_0,esk2_0))
    | v1_xboole_0(k10_yellow_6(esk1_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v3_yellow_6(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk3_0,k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(esk3_0,k10_yellow_6(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_137])).

cnf(c_0_149,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_80]),c_0_144])])).

cnf(c_0_150,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_80]),c_0_144])])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(esk3_0,k10_yellow_6(esk1_0,esk4_0))
    | v2_struct_0(esk12_3(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_146])).

cnf(c_0_152,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0)
    | ~ v4_orders_2(esk11_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_109]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_107])).

cnf(c_0_153,negated_conjecture,
    ( v1_xboole_0(k10_yellow_6(esk1_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk1_0,X1,esk2_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v3_yellow_6(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk3_0,k10_yellow_6(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_149])]),c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( m1_subset_1(esk3_0,k10_yellow_6(esk1_0,esk4_0))
    | v2_struct_0(esk12_3(esk1_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_129]),c_0_144]),c_0_130]),c_0_131]),c_0_132])]),c_0_133])).

cnf(c_0_155,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_119]),c_0_80]),c_0_24]),c_0_25])]),c_0_26]),c_0_107])).

fof(c_0_156,plain,(
    ! [X65] :
      ( ~ v1_xboole_0(X65)
      | X65 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_157,negated_conjecture,
    ( v1_xboole_0(k10_yellow_6(esk1_0,esk4_0))
    | v2_struct_0(esk12_3(esk1_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_144]),c_0_130]),c_0_155]),c_0_131]),c_0_132])]),c_0_133])).

cnf(c_0_158,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_156])).

cnf(c_0_159,negated_conjecture,
    ( v1_xboole_0(k10_yellow_6(esk1_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_157]),c_0_129]),c_0_130]),c_0_131]),c_0_132]),c_0_23]),c_0_24]),c_0_25])]),c_0_133]),c_0_26])).

cnf(c_0_160,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_161,negated_conjecture,
    ( k10_yellow_6(esk1_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_162,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_130]),c_0_155]),c_0_131]),c_0_132]),c_0_24]),c_0_25])]),c_0_133]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
