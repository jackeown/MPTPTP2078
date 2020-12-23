%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2066+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:11 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 384 expanded)
%              Number of clauses        :   52 ( 127 expanded)
%              Number of leaves         :    8 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  401 (5129 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   62 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_yellow19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow19)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t26_yellow19])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X19] :
      ( ( ~ v2_struct_0(esk2_3(X15,X16,X17))
        | ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v4_orders_2(esk2_3(X15,X16,X17))
        | ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v7_waybel_0(esk2_3(X15,X16,X17))
        | ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v3_yellow_6(esk2_3(X15,X16,X17),X15)
        | ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( l1_waybel_0(esk2_3(X15,X16,X17),X15)
        | ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r1_waybel_0(X15,esk2_3(X15,X16,X17),X16)
        | ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(X17,k10_yellow_6(X15,esk2_3(X15,X16,X17)))
        | ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ v3_yellow_6(X19,X15)
        | ~ l1_waybel_0(X19,X15)
        | ~ r1_waybel_0(X15,X19,X16)
        | ~ r2_hidden(X17,k10_yellow_6(X15,X19))
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_yellow19])])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X31,X32] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( ~ v2_struct_0(esk5_0)
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( v4_orders_2(esk5_0)
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( v7_waybel_0(esk5_0)
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( v3_yellow_6(esk5_0,esk3_0)
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( l1_waybel_0(esk5_0,esk3_0)
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( r1_waybel_0(esk3_0,esk5_0,esk4_0)
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( m1_subset_1(esk6_0,u1_struct_0(esk3_0))
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( r2_hidden(esk6_0,k10_yellow_6(esk3_0,esk5_0))
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( ~ r2_hidden(esk6_0,esk4_0)
        | ~ v4_pre_topc(esk4_0,esk3_0) )
      & ( v4_pre_topc(esk4_0,esk3_0)
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ v3_yellow_6(X31,esk3_0)
        | ~ l1_waybel_0(X31,esk3_0)
        | ~ r1_waybel_0(esk3_0,X31,esk4_0)
        | ~ m1_subset_1(X32,u1_struct_0(esk3_0))
        | ~ r2_hidden(X32,k10_yellow_6(esk3_0,X31))
        | r2_hidden(X32,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_11,plain,(
    ! [X25,X26] :
      ( ( ~ v4_pre_topc(X26,X25)
        | k2_pre_topc(X25,X26) = X26
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( ~ v2_pre_topc(X25)
        | k2_pre_topc(X25,X26) != X26
        | v4_pre_topc(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_12,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk6_0,k10_yellow_6(esk3_0,esk5_0))
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v4_orders_2(esk5_0)
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v7_waybel_0(esk5_0)
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v3_yellow_6(esk5_0,esk3_0)
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk3_0)
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk3_0,X1))
    | ~ v4_pre_topc(esk4_0,esk3_0)
    | ~ r1_waybel_0(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k2_pre_topc(esk3_0,esk4_0) = esk4_0
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_15])])).

cnf(c_0_27,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk5_0,esk4_0)
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk4_0)
    | ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0)
    | v2_struct_0(X1)
    | r2_hidden(X2,esk4_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v3_yellow_6(X1,esk3_0)
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ r1_waybel_0(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X2,k10_yellow_6(esk3_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ v4_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24])]),c_0_27]),c_0_28])).

fof(c_0_32,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | m1_subset_1(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_33,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_34,negated_conjecture,
    ( v2_struct_0(esk2_3(esk3_0,X1,X2))
    | r2_hidden(X2,esk4_0)
    | ~ r1_waybel_0(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)
    | ~ l1_waybel_0(esk2_3(esk3_0,X1,X2),esk3_0)
    | ~ v3_yellow_6(esk2_3(esk3_0,X1,X2),esk3_0)
    | ~ v7_waybel_0(esk2_3(esk3_0,X1,X2))
    | ~ v4_orders_2(esk2_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X2,k2_pre_topc(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_14]),c_0_15])]),c_0_16]),c_0_31])).

cnf(c_0_35,plain,
    ( r1_waybel_0(X1,esk2_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | r2_hidden(X1,esk4_0)
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,X1),esk3_0)
    | ~ v3_yellow_6(esk2_3(esk3_0,esk4_0,X1),esk3_0)
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_40,plain,
    ( l1_waybel_0(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | r2_hidden(X1,esk4_0)
    | ~ v3_yellow_6(esk2_3(esk3_0,esk4_0,X1),esk3_0)
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_14]),c_0_24]),c_0_15])]),c_0_16])).

cnf(c_0_44,plain,
    ( v3_yellow_6(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk2_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk1_2(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))
    | r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | r2_hidden(X1,esk4_0)
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_14]),c_0_24]),c_0_15])]),c_0_16])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk2_3(X1,X2,esk1_2(k2_pre_topc(X1,X2),X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(esk2_3(esk3_0,esk4_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | ~ m1_subset_1(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_50,plain,
    ( v7_waybel_0(esk2_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | ~ m1_subset_1(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_14]),c_0_24]),c_0_15])]),c_0_16])).

cnf(c_0_52,plain,
    ( v7_waybel_0(esk2_3(X1,X2,esk1_2(k2_pre_topc(X1,X2),X3)))
    | v2_struct_0(X1)
    | r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_46])).

cnf(c_0_53,plain,
    ( v4_orders_2(esk2_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | ~ m1_subset_1(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_14]),c_0_24]),c_0_15])]),c_0_16])).

cnf(c_0_55,plain,
    ( v4_orders_2(esk2_3(X1,X2,esk1_2(k2_pre_topc(X1,X2),X3)))
    | v2_struct_0(X1)
    | r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_42]),c_0_46])).

fof(c_0_56,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_57,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | r1_tarski(X21,k2_pre_topc(X20,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_14]),c_0_24]),c_0_15])]),c_0_16])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_46]),c_0_24]),c_0_15])])).

cnf(c_0_63,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_64,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0)
    | k2_pre_topc(esk3_0,esk4_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_24]),c_0_14]),c_0_15])])).

cnf(c_0_67,negated_conjecture,
    ( k2_pre_topc(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_24]),c_0_15])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])]),c_0_31]),
    [proof]).

%------------------------------------------------------------------------------
