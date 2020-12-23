%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2067+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:12 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 (122416 expanded)
%              Number of clauses        :  112 (39572 expanded)
%              Number of leaves         :   15 (29861 expanded)
%              Depth                    :   29
%              Number of atoms          :  885 (1594549 expanded)
%              Number of equality atoms :    4 (  88 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   54 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_yellow19,conjecture,(
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
                    ( ~ v1_xboole_0(X4)
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
                    & r2_hidden(X2,X4)
                    & r1_waybel_7(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

fof(fc3_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ( v1_subset_1(k2_yellow19(X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
        & v2_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow19)).

fof(fc2_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => ( ~ v1_xboole_0(k2_yellow19(X1,X2))
        & v13_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow19)).

fof(dt_k2_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k2_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow19)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(c_0_15,negated_conjecture,(
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
                      ( ~ v1_xboole_0(X4)
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
                      & r2_hidden(X2,X4)
                      & r1_waybel_7(X1,X4,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_yellow19])).

fof(c_0_16,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r3_waybel_9(X28,X29,X30)
        | r1_waybel_7(X28,k2_yellow19(X28,X29),X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ r1_waybel_7(X28,k2_yellow19(X28,X29),X30)
        | r3_waybel_9(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

fof(c_0_17,negated_conjecture,(
    ! [X46] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
      & ( ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
        | v1_xboole_0(X46)
        | ~ v1_subset_1(X46,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
        | ~ v2_waybel_0(X46,k3_yellow_1(k2_struct_0(esk2_0)))
        | ~ v13_waybel_0(X46,k3_yellow_1(k2_struct_0(esk2_0)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
        | ~ r2_hidden(esk3_0,X46)
        | ~ r1_waybel_7(esk2_0,X46,esk4_0) )
      & ( ~ v1_xboole_0(esk5_0)
        | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
        | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
        | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
        | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
        | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( r2_hidden(esk3_0,esk5_0)
        | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( r1_waybel_7(esk2_0,esk5_0,esk4_0)
        | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_18,plain,(
    ! [X33,X34,X35,X37] :
      ( ( ~ v2_struct_0(esk1_3(X33,X34,X35))
        | ~ r2_hidden(X35,k2_pre_topc(X33,X34))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v4_orders_2(esk1_3(X33,X34,X35))
        | ~ r2_hidden(X35,k2_pre_topc(X33,X34))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v7_waybel_0(esk1_3(X33,X34,X35))
        | ~ r2_hidden(X35,k2_pre_topc(X33,X34))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( l1_waybel_0(esk1_3(X33,X34,X35),X33)
        | ~ r2_hidden(X35,k2_pre_topc(X33,X34))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r1_waybel_0(X33,esk1_3(X33,X34,X35),X34)
        | ~ r2_hidden(X35,k2_pre_topc(X33,X34))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r3_waybel_9(X33,esk1_3(X33,X34,X35),X35)
        | ~ r2_hidden(X35,k2_pre_topc(X33,X34))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v2_struct_0(X37)
        | ~ v4_orders_2(X37)
        | ~ v7_waybel_0(X37)
        | ~ l1_waybel_0(X37,X33)
        | ~ r1_waybel_0(X33,X37,X34)
        | ~ r3_waybel_9(X33,X37,X35)
        | r2_hidden(X35,k2_pre_topc(X33,X34))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_yellow19])])])])])])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r3_waybel_9(X1,esk1_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_27,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,X1),esk4_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk2_0,X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r3_waybel_9(esk2_0,esk1_3(esk2_0,esk3_0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_29,plain,(
    ! [X25,X26,X27] :
      ( ( r1_waybel_0(X25,X26,X27)
        | ~ r2_hidden(X27,k2_yellow19(X25,X26))
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) )
      & ( m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r2_hidden(X27,k2_yellow19(X25,X26))
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) )
      & ( ~ r1_waybel_0(X25,X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | r2_hidden(X27,k2_yellow19(X25,X26))
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t11_yellow19])])])])])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | ~ v7_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v4_orders_2(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( v7_waybel_0(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_34,plain,(
    ! [X16,X17] :
      ( ( v1_subset_1(k2_yellow19(X16,X17),u1_struct_0(k3_yellow_1(k2_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v2_struct_0(X17)
        | ~ v4_orders_2(X17)
        | ~ v7_waybel_0(X17)
        | ~ l1_waybel_0(X17,X16) )
      & ( v2_waybel_0(k2_yellow19(X16,X17),k3_yellow_1(k2_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v2_struct_0(X17)
        | ~ v4_orders_2(X17)
        | ~ v7_waybel_0(X17)
        | ~ l1_waybel_0(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_yellow19])])])])).

cnf(c_0_35,plain,
    ( l1_waybel_0(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( v4_orders_2(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_37,plain,(
    ! [X14,X15] :
      ( ( ~ v1_xboole_0(k2_yellow19(X14,X15))
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14) )
      & ( v13_waybel_0(k2_yellow19(X14,X15),k3_yellow_1(k2_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_yellow19])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,k2_yellow19(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_40,plain,
    ( r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v7_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v4_orders_2(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v2_struct_0(X9)
      | ~ l1_waybel_0(X9,X8)
      | m1_subset_1(k2_yellow19(X8,X9),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X8))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_yellow19])])])).

fof(c_0_44,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_45,plain,
    ( v1_subset_1(k2_yellow19(X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk2_0,esk3_0,X1),esk2_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( v4_orders_2(esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_48,plain,
    ( v2_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( v13_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_0,k2_yellow19(esk2_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk2_0,X1,esk3_0)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_23]),c_0_39])])).

cnf(c_0_51,negated_conjecture,
    ( r1_waybel_0(esk2_0,esk1_3(esk2_0,esk3_0,X1),esk3_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v4_orders_2(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_20])]),c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k2_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_waybel_7(esk2_0,X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( v1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,X1)),u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_39])]),c_0_23]),c_0_47]),c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( v2_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,X1)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_39])]),c_0_23]),c_0_47]),c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( v13_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,X1)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_39])]),c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,X1)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_20])]),c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | ~ v7_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v4_orders_2(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(esk1_3(esk2_0,esk3_0,X1))
    | m1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,X1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_39])]),c_0_23])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_waybel_7(esk2_0,X1,esk4_0)
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | ~ r2_hidden(esk3_0,X1)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(csr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | v1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_32]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | v2_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_32]),c_0_20])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | v13_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_20])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)))
    | r2_hidden(esk3_0,esk5_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_20])])).

cnf(c_0_69,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_46]),c_0_20])]),c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | ~ v4_orders_2(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_42]),c_0_20])]),c_0_53])).

cnf(c_0_71,negated_conjecture,
    ( v1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_53]),c_0_20])])).

cnf(c_0_72,negated_conjecture,
    ( v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_53]),c_0_20])])).

cnf(c_0_73,negated_conjecture,
    ( v2_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_53]),c_0_20])])).

cnf(c_0_74,negated_conjecture,
    ( v13_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_20])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk3_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_53]),c_0_20])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ m1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_32]),c_0_68]),c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_47]),c_0_20])]),c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    | ~ r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_71]),c_0_72]),c_0_73]),c_0_74]),c_0_53]),c_0_75])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_32]),c_0_20])]),c_0_76])).

fof(c_0_81,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ l1_struct_0(X31)
      | v1_xboole_0(X32)
      | ~ v1_subset_1(X32,u1_struct_0(k3_yellow_1(k2_struct_0(X31))))
      | ~ v2_waybel_0(X32,k3_yellow_1(k2_struct_0(X31)))
      | ~ v13_waybel_0(X32,k3_yellow_1(k2_struct_0(X31)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X31)))))
      | X32 = k2_yellow19(X31,k3_yellow19(X31,k2_struct_0(X31),X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_46]),c_0_20])]),c_0_53]),c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_21]),c_0_25]),c_0_20]),c_0_22])]),c_0_23]),c_0_32])).

fof(c_0_84,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_struct_0(k3_yellow19(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,k3_yellow_1(X11))
        | ~ v13_waybel_0(X12,k3_yellow_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11)))) )
      & ( v6_waybel_0(k3_yellow19(X10,X11,X12),X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,k3_yellow_1(X11))
        | ~ v13_waybel_0(X12,k3_yellow_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11)))) )
      & ( l1_waybel_0(k3_yellow19(X10,X11,X12),X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,k3_yellow_1(X11))
        | ~ v13_waybel_0(X12,k3_yellow_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_82]),c_0_21]),c_0_25]),c_0_20]),c_0_22])]),c_0_23]),c_0_53])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_83])).

cnf(c_0_88,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_89,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_struct_0(k3_yellow19(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v1_xboole_0(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v1_xboole_0(X24)
        | ~ v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))
        | ~ v2_waybel_0(X24,k3_yellow_1(X23))
        | ~ v13_waybel_0(X24,k3_yellow_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))) )
      & ( v6_waybel_0(k3_yellow19(X22,X23,X24),X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v1_xboole_0(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v1_xboole_0(X24)
        | ~ v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))
        | ~ v2_waybel_0(X24,k3_yellow_1(X23))
        | ~ v13_waybel_0(X24,k3_yellow_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))) )
      & ( v7_waybel_0(k3_yellow19(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v1_xboole_0(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v1_xboole_0(X24)
        | ~ v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))
        | ~ v2_waybel_0(X24,k3_yellow_1(X23))
        | ~ v13_waybel_0(X24,k3_yellow_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_90,plain,(
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
      & ( v3_orders_2(k3_yellow19(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( v4_orders_2(k3_yellow19(X18,X19,X20))
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
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_91,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_92,negated_conjecture,
    ( k2_yellow19(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0)) = esk5_0
    | ~ v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | ~ v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_39])]),c_0_87]),c_0_23])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0),X1)
    | v2_struct_0(X1)
    | ~ v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_86]),c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_95,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_96,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | m1_subset_1(k2_struct_0(X7),k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_97,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_98,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( r1_waybel_0(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),X1)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | ~ v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_39])]),c_0_23])).

cnf(c_0_100,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0),X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_102,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_103,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_104,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | ~ v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_86]),c_0_87])).

cnf(c_0_105,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_86]),c_0_87])).

cnf(c_0_106,negated_conjecture,
    ( r1_waybel_0(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),X1)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_94]),c_0_95]),c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_39])]),c_0_23])).

cnf(c_0_108,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),X1)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ r1_waybel_7(esk2_0,esk5_0,X1)
    | ~ v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_92]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_94]),c_0_95]),c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v4_orders_2(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_94]),c_0_95])).

cnf(c_0_111,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_112,negated_conjecture,
    ( r1_waybel_0(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),X1)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),X1)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ r1_waybel_7(esk2_0,esk5_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_94]),c_0_95]),c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_102]),c_0_39])]),c_0_23])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_102]),c_0_39])]),c_0_23])).

cnf(c_0_116,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk2_0,X2,X1)
    | ~ r1_waybel_0(esk2_0,X2,esk3_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_25]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_118,negated_conjecture,
    ( r1_waybel_0(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),esk3_0)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_83])).

cnf(c_0_119,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),X1)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ r1_waybel_7(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_107]),c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk5_0,esk4_0)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_121,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk2_0)))
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_86]),c_0_87])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0))
    | ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_107]),c_0_115]),c_0_114])).

cnf(c_0_123,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0),esk4_0)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_20])])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk5_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_94]),c_0_95])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_20])])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_39])]),c_0_23])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | v1_xboole_0(k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_102]),c_0_39])])).

cnf(c_0_128,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v7_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v4_orders_2(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_127])).

cnf(c_0_129,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ v4_orders_2(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_42]),c_0_20])]),c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( v1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_127]),c_0_20])])).

cnf(c_0_131,negated_conjecture,
    ( v2_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_127]),c_0_20])])).

cnf(c_0_132,negated_conjecture,
    ( v13_waybel_0(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k3_yellow_1(k2_struct_0(esk2_0)))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_127]),c_0_20])])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk3_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)))
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_127]),c_0_20])])).

cnf(c_0_134,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ l1_waybel_0(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_47]),c_0_20])]),c_0_127])).

cnf(c_0_135,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | ~ m1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_130]),c_0_131]),c_0_132]),c_0_127]),c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk4_0)
    | v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_46]),c_0_20])]),c_0_127])).

cnf(c_0_137,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0))
    | m1_subset_1(k2_yellow19(esk2_0,esk1_3(esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_127]),c_0_20])])).

fof(c_0_138,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_xboole_0(k2_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_139,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137])).

cnf(c_0_140,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_139]),c_0_21]),c_0_25]),c_0_20]),c_0_22])]),c_0_23]),c_0_127])).

cnf(c_0_142,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_39])]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
