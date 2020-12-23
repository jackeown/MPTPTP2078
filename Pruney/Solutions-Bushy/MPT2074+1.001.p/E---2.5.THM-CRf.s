%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2074+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  174 (14188234 expanded)
%              Number of clauses        :  143 (4702553 expanded)
%              Number of leaves         :   15 (3704128 expanded)
%              Depth                    :   76
%              Number of atoms          : 1139 (172072242 expanded)
%              Number of equality atoms :    3 (33075 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r1_waybel_7(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow19)).

fof(dt_k2_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k2_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow19)).

fof(l38_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r3_waybel_9(X1,X2,X3) ) ) )
       => v1_compts_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(l37_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).

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

fof(t17_yellow19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_compts_1(X1)
        <=> ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
             => ? [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                  & r1_waybel_7(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_yellow19])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ l1_struct_0(X6)
      | v2_struct_0(X7)
      | ~ l1_waybel_0(X7,X6)
      | m1_subset_1(k2_yellow19(X6,X7),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X6))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_yellow19])])])).

fof(c_0_17,plain,(
    ! [X30,X32] :
      ( ( ~ v2_struct_0(esk4_1(X30))
        | v1_compts_1(X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v4_orders_2(esk4_1(X30))
        | v1_compts_1(X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v7_waybel_0(esk4_1(X30))
        | v1_compts_1(X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( l1_waybel_0(esk4_1(X30),X30)
        | v1_compts_1(X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk4_1(X30),k6_yellow_6(X30))
        | v1_compts_1(X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ r3_waybel_9(X30,esk4_1(X30),X32)
        | v1_compts_1(X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).

fof(c_0_18,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ( v1_subset_1(k2_yellow19(X19,X20),u1_struct_0(k3_yellow_1(k2_struct_0(X19))))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19) )
      & ( v2_waybel_0(k2_yellow19(X19,X20),k3_yellow_1(k2_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_yellow19])])])])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ( ~ v1_xboole_0(k2_yellow19(X17,X18))
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17)
        | v2_struct_0(X18)
        | ~ l1_waybel_0(X18,X17) )
      & ( v13_waybel_0(k2_yellow19(X17,X18),k3_yellow_1(k2_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17)
        | v2_struct_0(X18)
        | ~ l1_waybel_0(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_yellow19])])])])).

fof(c_0_21,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r3_waybel_9(X33,X34,X35)
        | r1_waybel_7(X33,k2_yellow19(X33,X34),X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r1_waybel_7(X33,k2_yellow19(X33,X34),X35)
        | r3_waybel_9(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

fof(c_0_22,negated_conjecture,(
    ! [X46,X47] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & ( ~ v1_xboole_0(esk6_0)
        | ~ v1_compts_1(esk5_0) )
      & ( v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
        | ~ v1_compts_1(esk5_0) )
      & ( v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v1_compts_1(esk5_0) )
      & ( v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v1_compts_1(esk5_0) )
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
        | ~ v1_compts_1(esk5_0) )
      & ( ~ m1_subset_1(X46,u1_struct_0(esk5_0))
        | ~ r1_waybel_7(esk5_0,esk6_0,X46)
        | ~ v1_compts_1(esk5_0) )
      & ( m1_subset_1(esk7_1(X47),u1_struct_0(esk5_0))
        | v1_xboole_0(X47)
        | ~ v1_subset_1(X47,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
        | ~ v2_waybel_0(X47,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v13_waybel_0(X47,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
        | v1_compts_1(esk5_0) )
      & ( r1_waybel_7(esk5_0,X47,esk7_1(X47))
        | v1_xboole_0(X47)
        | ~ v1_subset_1(X47,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
        | ~ v2_waybel_0(X47,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ v13_waybel_0(X47,k3_yellow_1(k2_struct_0(esk5_0)))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
        | v1_compts_1(esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k2_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( l1_waybel_0(esk4_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v2_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v4_orders_2(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( v7_waybel_0(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( v13_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r1_waybel_7(esk5_0,X1,esk7_1(X1))
    | v1_xboole_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_1(X1),u1_struct_0(esk5_0))
    | v1_xboole_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | m1_subset_1(k2_yellow19(X1,esk4_1(X1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_38,plain,
    ( v1_compts_1(X1)
    | v2_waybel_0(k2_yellow19(X1,esk4_1(X1)),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_25]),c_0_28]),c_0_29]),c_0_26])).

cnf(c_0_39,plain,
    ( v1_compts_1(X1)
    | v13_waybel_0(k2_yellow19(X1,esk4_1(X1)),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_40,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk4_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( r3_waybel_9(esk5_0,X1,esk7_1(k2_yellow19(esk5_0,X1)))
    | v1_compts_1(esk5_0)
    | v1_xboole_0(k2_yellow19(esk5_0,X1))
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_subset_1(k2_yellow19(esk5_0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v13_waybel_0(k2_yellow19(esk5_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(k2_yellow19(esk5_0,X1),k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(k2_yellow19(esk5_0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | m1_subset_1(k2_yellow19(esk5_0,esk4_1(esk5_0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_waybel_0(k2_yellow19(esk5_0,esk4_1(esk5_0)),k3_yellow_1(k2_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v13_waybel_0(k2_yellow19(esk5_0,esk4_1(esk5_0)),k3_yellow_1(k2_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_45,plain,
    ( v1_subset_1(k2_yellow19(X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0))
    | ~ v1_subset_1(k2_yellow19(esk5_0,esk4_1(esk5_0)),u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_34])]),c_0_35]),c_0_36]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_47,plain,
    ( v1_compts_1(X1)
    | v1_subset_1(k2_yellow19(X1,esk4_1(X1)),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_25]),c_0_28]),c_0_29]),c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0))
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_54,plain,(
    ! [X27,X28] :
      ( ( m1_subset_1(esk3_2(X27,X28),u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | ~ v1_compts_1(X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( r3_waybel_9(X27,X28,esk3_2(X27,X28))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | ~ v1_compts_1(X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

fof(c_0_55,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_struct_0(k3_yellow19(X8,X9,X10))
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) )
      & ( v6_waybel_0(k3_yellow19(X8,X9,X10),X8)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) )
      & ( l1_waybel_0(k3_yellow19(X8,X9,X10),X8)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_xboole_0(k2_yellow19(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(esk4_1(esk5_0))
    | ~ v1_xboole_0(esk6_0)
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_59]),c_0_58])]),c_0_35])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X3,X1,X2))
    | v2_struct_0(X3)
    | m1_subset_1(esk3_2(X3,k3_yellow19(X3,X1,X2)),u1_struct_0(X3))
    | ~ v1_compts_1(X3)
    | ~ v2_pre_topc(X3)
    | ~ v7_waybel_0(k3_yellow19(X3,X1,X2))
    | ~ v4_orders_2(k3_yellow19(X3,X1,X2))
    | ~ l1_pre_topc(X3)
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_24]),c_0_33]),c_0_34])]),c_0_35]),c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(esk4_1(esk5_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_24]),c_0_33]),c_0_34])]),c_0_35]),c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_69,negated_conjecture,
    ( v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(esk5_0)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

fof(c_0_71,plain,(
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

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_52])).

cnf(c_0_73,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_25]),c_0_65]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_76,plain,(
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

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_69]),c_0_68]),c_0_52])).

cnf(c_0_78,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_79,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | m1_subset_1(k2_struct_0(X5),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_25]),c_0_65]),c_0_66])).

cnf(c_0_81,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_68]),c_0_69]),c_0_52])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_58])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_33]),c_0_34])]),c_0_35]),c_0_52])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_84]),c_0_58])]),c_0_35])).

cnf(c_0_86,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_24]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_73]),c_0_25]),c_0_65]),c_0_66])).

cnf(c_0_89,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r1_waybel_7(esk5_0,esk6_0,X1)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_90,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r3_waybel_9(X36,k3_yellow19(X36,k2_struct_0(X36),X37),X38)
        | r1_waybel_7(X36,X37,X38)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v1_xboole_0(X37)
        | ~ v1_subset_1(X37,u1_struct_0(k3_yellow_1(k2_struct_0(X36))))
        | ~ v2_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
        | ~ v13_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36)))))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ r1_waybel_7(X36,X37,X38)
        | r3_waybel_9(X36,k3_yellow19(X36,k2_struct_0(X36),X37),X38)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v1_xboole_0(X37)
        | ~ v1_subset_1(X37,u1_struct_0(k3_yellow_1(k2_struct_0(X36))))
        | ~ v2_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
        | ~ v13_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36)))))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow19])])])])])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_75]),c_0_69]),c_0_68]),c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ r1_waybel_7(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_52])).

cnf(c_0_93,plain,
    ( r1_waybel_7(X1,X2,X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_78]),c_0_25]),c_0_65]),c_0_66])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0),X1)
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_33]),c_0_34])]),c_0_35]),c_0_65]),c_0_66])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_68]),c_0_69]),c_0_86])).

fof(c_0_97,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | k2_struct_0(X4) = u1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_75]),c_0_69]),c_0_68]),c_0_52])).

cnf(c_0_99,plain,
    ( r3_waybel_9(X1,X2,esk3_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_100,plain,(
    ! [X16] :
      ( v2_struct_0(X16)
      | ~ l1_struct_0(X16)
      | ~ v1_xboole_0(u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_83]),c_0_33]),c_0_34])]),c_0_35]),c_0_86])).

cnf(c_0_102,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_waybel_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0),esk5_0)
    | ~ m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_33]),c_0_34])]),c_0_35]),c_0_52])).

cnf(c_0_104,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_58])])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ l1_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0),esk5_0)
    | ~ m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_102]),c_0_58])])).

cnf(c_0_107,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_58])]),c_0_35])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ l1_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_102]),c_0_58])])).

cnf(c_0_110,negated_conjecture,
    ( v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_102]),c_0_58])])).

cnf(c_0_111,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_61]),c_0_109]),c_0_58])]),c_0_35]),c_0_110]),c_0_66])).

cnf(c_0_112,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_73]),c_0_109]),c_0_58])]),c_0_35]),c_0_110]),c_0_66])).

cnf(c_0_113,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_78]),c_0_109]),c_0_58])]),c_0_35]),c_0_110]),c_0_66])).

cnf(c_0_114,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))
    | ~ v1_compts_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_102]),c_0_58])])).

cnf(c_0_115,negated_conjecture,
    ( v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v1_compts_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_102]),c_0_58])])).

cnf(c_0_116,negated_conjecture,
    ( v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v1_compts_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_102]),c_0_58])])).

cnf(c_0_117,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_116]),c_0_52])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_117]),c_0_58])]),c_0_35])).

cnf(c_0_119,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_24]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ r1_waybel_7(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_119])).

cnf(c_0_121,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0),X1)
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_93]),c_0_33]),c_0_34])]),c_0_35]),c_0_65]),c_0_66])).

cnf(c_0_122,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_75]),c_0_69]),c_0_68]),c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_102]),c_0_58])])).

cnf(c_0_124,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ l1_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_99]),c_0_33]),c_0_34])]),c_0_35]),c_0_107]),c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_61]),c_0_109]),c_0_58])]),c_0_35]),c_0_110]),c_0_66])).

cnf(c_0_126,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_73]),c_0_109]),c_0_58])]),c_0_35]),c_0_110]),c_0_66])).

cnf(c_0_127,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_78]),c_0_109]),c_0_58])]),c_0_35]),c_0_110]),c_0_66])).

cnf(c_0_128,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_114]),c_0_115]),c_0_116]),c_0_119])).

cnf(c_0_129,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_128]),c_0_58])]),c_0_35])).

cnf(c_0_130,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_129]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_131,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_131]),c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_68]),c_0_69]),c_0_130])).

cnf(c_0_135,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_73]),c_0_25]),c_0_131]),c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_75]),c_0_69]),c_0_68]),c_0_130])).

cnf(c_0_137,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ r1_waybel_7(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_130])).

cnf(c_0_138,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_78]),c_0_25]),c_0_131]),c_0_132])).

cnf(c_0_139,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0),X1)
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_93]),c_0_33]),c_0_34])]),c_0_35]),c_0_131]),c_0_132])).

cnf(c_0_140,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_68]),c_0_69]),c_0_130])).

cnf(c_0_141,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_75]),c_0_69]),c_0_68]),c_0_130])).

cnf(c_0_142,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_83]),c_0_33]),c_0_34])]),c_0_35]),c_0_130])).

cnf(c_0_143,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ r3_waybel_9(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_102]),c_0_58])])).

cnf(c_0_144,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_102]),c_0_58])])).

cnf(c_0_145,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ l1_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0),esk5_0)
    | ~ m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_99]),c_0_33]),c_0_34])]),c_0_35]),c_0_130])).

cnf(c_0_146,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | m1_subset_1(esk3_2(esk5_0,k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_144]),c_0_58])]),c_0_35])).

cnf(c_0_147,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ l1_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_148,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_102]),c_0_58])])).

cnf(c_0_149,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_150,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v7_waybel_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_61]),c_0_109]),c_0_58])]),c_0_35]),c_0_148]),c_0_132])).

cnf(c_0_151,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk5_0),esk6_0))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_65]),c_0_66])).

cnf(c_0_152,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_73]),c_0_109]),c_0_58])]),c_0_35]),c_0_148]),c_0_132])).

cnf(c_0_153,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk5_0),esk6_0))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_102]),c_0_58])])).

cnf(c_0_154,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0))
    | ~ v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))
    | ~ v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_78]),c_0_109]),c_0_58])]),c_0_35]),c_0_148]),c_0_132])).

cnf(c_0_155,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | ~ v1_compts_1(esk5_0)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk5_0),esk6_0))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_116]),c_0_115])).

cnf(c_0_156,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_114]),c_0_115]),c_0_116]),c_0_130])).

cnf(c_0_157,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk5_0),esk6_0))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_155,c_0_52])).

cnf(c_0_158,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk5_0,u1_struct_0(esk5_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_156]),c_0_58])]),c_0_35])).

cnf(c_0_159,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk5_0,esk4_1(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_109]),c_0_58])]),c_0_35])).

cnf(c_0_160,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_159]),c_0_58])]),c_0_35])).

cnf(c_0_161,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_24]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_162,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk5_0),esk6_0))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_155,c_0_161])).

cnf(c_0_163,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_158]),c_0_109]),c_0_58])]),c_0_35])).

cnf(c_0_164,negated_conjecture,
    ( v2_struct_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_163]),c_0_58])]),c_0_35])).

cnf(c_0_165,negated_conjecture,
    ( v1_compts_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_164]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_166,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_165])])).

cnf(c_0_167,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_102]),c_0_58])])).

cnf(c_0_168,negated_conjecture,
    ( v13_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_165])])).

cnf(c_0_169,negated_conjecture,
    ( v2_waybel_0(esk6_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_165])])).

cnf(c_0_170,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_165])])).

cnf(c_0_171,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk5_0),esk6_0))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_167]),c_0_168]),c_0_169])]),c_0_170])).

cnf(c_0_172,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_158]),c_0_109]),c_0_58])]),c_0_35])).

cnf(c_0_173,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_172]),c_0_58])]),c_0_35]),
    [proof]).

%------------------------------------------------------------------------------
