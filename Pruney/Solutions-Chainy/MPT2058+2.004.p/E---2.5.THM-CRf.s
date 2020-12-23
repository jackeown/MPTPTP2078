%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  103 (1786 expanded)
%              Number of clauses        :   72 ( 705 expanded)
%              Number of leaves         :   15 ( 453 expanded)
%              Depth                    :   14
%              Number of atoms          :  507 (9396 expanded)
%              Number of equality atoms :   20 ( 480 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(rc20_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v1_zfmisc_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc20_struct_0)).

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

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(c_0_15,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_16,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))
    & v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))
    & v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( ~ r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)
      | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0) )
    & ( r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)
      | r1_waybel_7(esk4_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_23,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v2_struct_0(k3_yellow19(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27)
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v1_xboole_0(X29)
        | ~ v2_waybel_0(X29,k3_yellow_1(X28))
        | ~ v13_waybel_0(X29,k3_yellow_1(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28)))) )
      & ( v3_orders_2(k3_yellow19(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27)
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v1_xboole_0(X29)
        | ~ v2_waybel_0(X29,k3_yellow_1(X28))
        | ~ v13_waybel_0(X29,k3_yellow_1(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28)))) )
      & ( v4_orders_2(k3_yellow19(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27)
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v1_xboole_0(X29)
        | ~ v2_waybel_0(X29,k3_yellow_1(X28))
        | ~ v13_waybel_0(X29,k3_yellow_1(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28)))) )
      & ( v6_waybel_0(k3_yellow19(X27,X28,X29),X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27)
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v1_xboole_0(X29)
        | ~ v2_waybel_0(X29,k3_yellow_1(X28))
        | ~ v13_waybel_0(X29,k3_yellow_1(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

fof(c_0_24,plain,(
    ! [X23] : k3_yellow_1(X23) = k3_lattice3(k1_lattice3(X23)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,plain,(
    ! [X21] :
      ( ( m1_subset_1(esk3_1(X21),k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) )
      & ( ~ v1_xboole_0(esk3_1(X21))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) )
      & ( v1_zfmisc_1(esk3_1(X21))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc20_struct_0])])])])])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v2_struct_0(k3_yellow19(X24,X25,X26))
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( v6_waybel_0(k3_yellow19(X24,X25,X26),X24)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( l1_waybel_0(k3_yellow19(X24,X25,X26),X24)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

fof(c_0_32,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | v1_xboole_0(X37)
      | ~ v1_subset_1(X37,u1_struct_0(k3_yellow_1(k2_struct_0(X36))))
      | ~ v2_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
      | ~ v13_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36)))))
      | X37 = k2_yellow19(X36,k3_yellow19(X36,k2_struct_0(X36),X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

cnf(c_0_33,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_44,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v2_struct_0(k3_yellow19(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v1_xboole_0(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v1_xboole_0(X32)
        | ~ v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))
        | ~ v2_waybel_0(X32,k3_yellow_1(X31))
        | ~ v13_waybel_0(X32,k3_yellow_1(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31)))) )
      & ( v6_waybel_0(k3_yellow19(X30,X31,X32),X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v1_xboole_0(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v1_xboole_0(X32)
        | ~ v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))
        | ~ v2_waybel_0(X32,k3_yellow_1(X31))
        | ~ v13_waybel_0(X32,k3_yellow_1(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31)))) )
      & ( v7_waybel_0(k3_yellow19(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v1_xboole_0(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v1_xboole_0(X32)
        | ~ v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))
        | ~ v2_waybel_0(X32,k3_yellow_1(X31))
        | ~ v13_waybel_0(X32,k3_yellow_1(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_45,plain,(
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

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_53,plain,(
    ! [X19] :
      ( ~ l1_struct_0(X19)
      | m1_subset_1(k2_struct_0(X19),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_34]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_64,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_65,plain,(
    ! [X18] :
      ( ~ l1_struct_0(X18)
      | k2_struct_0(X18) = u1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk3_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( esk3_1(esk4_0) = u1_struct_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_69,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_34]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( r1_waybel_7(esk4_0,k2_yellow19(esk4_0,X1),esk6_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk4_0,X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_30])]),c_0_42])).

cnf(c_0_72,negated_conjecture,
    ( r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)
    | r1_waybel_7(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_49]),c_0_62]),c_0_50]),c_0_51])]),c_0_42]),c_0_52]),c_0_41])])).

cnf(c_0_74,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_41])]),c_0_42])).

cnf(c_0_75,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_41])]),c_0_42])).

cnf(c_0_77,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)
    | v1_xboole_0(k2_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_64]),c_0_41])]),c_0_42])).

cnf(c_0_78,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_49]),c_0_62]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_81,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_41])]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_75]),c_0_41])]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(k2_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_64]),c_0_41])]),c_0_42])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( ~ r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_87,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_75]),c_0_81]),c_0_41])]),c_0_82])])).

cnf(c_0_88,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_75]),c_0_41])]),c_0_76])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk6_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_75])).

cnf(c_0_93,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_75]),c_0_41])]),c_0_76])).

cnf(c_0_94,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),X1)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_73]),c_0_60]),c_0_30])]),c_0_42])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_41])])).

cnf(c_0_98,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_41]),c_0_95])]),c_0_42])).

cnf(c_0_99,negated_conjecture,
    ( r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),X1)
    | v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_75]),c_0_88]),c_0_81]),c_0_82]),c_0_41])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

cnf(c_0_101,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_98]),c_0_59])]),c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_101]),c_0_41]),c_0_95])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.031 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.13/0.39  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(rc20_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc20_struct_0)).
% 0.13/0.39  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.13/0.39  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.13/0.39  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.13/0.39  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 0.13/0.39  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.13/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.39  fof(c_0_15, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.39  fof(c_0_16, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.13/0.39  fof(c_0_18, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  cnf(c_0_19, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_20, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_21, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  fof(c_0_22, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((((~v1_xboole_0(esk5_0)&v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))&v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|~r1_waybel_7(esk4_0,esk5_0,esk6_0))&(r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|r1_waybel_7(esk4_0,esk5_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.39  fof(c_0_23, plain, ![X27, X28, X29]:((((~v2_struct_0(k3_yellow19(X27,X28,X29))|(v2_struct_0(X27)|~l1_struct_0(X27)|v1_xboole_0(X28)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|v1_xboole_0(X29)|~v2_waybel_0(X29,k3_yellow_1(X28))|~v13_waybel_0(X29,k3_yellow_1(X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28))))))&(v3_orders_2(k3_yellow19(X27,X28,X29))|(v2_struct_0(X27)|~l1_struct_0(X27)|v1_xboole_0(X28)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|v1_xboole_0(X29)|~v2_waybel_0(X29,k3_yellow_1(X28))|~v13_waybel_0(X29,k3_yellow_1(X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28)))))))&(v4_orders_2(k3_yellow19(X27,X28,X29))|(v2_struct_0(X27)|~l1_struct_0(X27)|v1_xboole_0(X28)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|v1_xboole_0(X29)|~v2_waybel_0(X29,k3_yellow_1(X28))|~v13_waybel_0(X29,k3_yellow_1(X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28)))))))&(v6_waybel_0(k3_yellow19(X27,X28,X29),X27)|(v2_struct_0(X27)|~l1_struct_0(X27)|v1_xboole_0(X28)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|v1_xboole_0(X29)|~v2_waybel_0(X29,k3_yellow_1(X28))|~v13_waybel_0(X29,k3_yellow_1(X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X28))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.13/0.39  fof(c_0_24, plain, ![X23]:k3_yellow_1(X23)=k3_lattice3(k1_lattice3(X23)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.39  cnf(c_0_25, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  fof(c_0_27, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  fof(c_0_28, plain, ![X21]:(((m1_subset_1(esk3_1(X21),k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~l1_struct_0(X21)))&(~v1_xboole_0(esk3_1(X21))|(v2_struct_0(X21)|~l1_struct_0(X21))))&(v1_zfmisc_1(esk3_1(X21))|(v2_struct_0(X21)|~l1_struct_0(X21)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc20_struct_0])])])])])).
% 0.13/0.39  cnf(c_0_29, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_31, plain, ![X24, X25, X26]:(((~v2_struct_0(k3_yellow19(X24,X25,X26))|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))&(v6_waybel_0(k3_yellow19(X24,X25,X26),X24)|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))))))&(l1_waybel_0(k3_yellow19(X24,X25,X26),X24)|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.13/0.39  fof(c_0_32, plain, ![X36, X37]:(v2_struct_0(X36)|~l1_struct_0(X36)|(v1_xboole_0(X37)|~v1_subset_1(X37,u1_struct_0(k3_yellow_1(k2_struct_0(X36))))|~v2_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))|~v13_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36)))))|X37=k2_yellow19(X36,k3_yellow19(X36,k2_struct_0(X36),X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.13/0.39  cnf(c_0_33, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_34, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.39  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_40, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_43, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  fof(c_0_44, plain, ![X30, X31, X32]:(((~v2_struct_0(k3_yellow19(X30,X31,X32))|(v2_struct_0(X30)|~l1_struct_0(X30)|v1_xboole_0(X31)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|v1_xboole_0(X32)|~v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))|~v2_waybel_0(X32,k3_yellow_1(X31))|~v13_waybel_0(X32,k3_yellow_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31))))))&(v6_waybel_0(k3_yellow19(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_struct_0(X30)|v1_xboole_0(X31)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|v1_xboole_0(X32)|~v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))|~v2_waybel_0(X32,k3_yellow_1(X31))|~v13_waybel_0(X32,k3_yellow_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31)))))))&(v7_waybel_0(k3_yellow19(X30,X31,X32))|(v2_struct_0(X30)|~l1_struct_0(X30)|v1_xboole_0(X31)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|v1_xboole_0(X32)|~v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))|~v2_waybel_0(X32,k3_yellow_1(X31))|~v13_waybel_0(X32,k3_yellow_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.13/0.39  fof(c_0_45, plain, ![X33, X34, X35]:((~r3_waybel_9(X33,X34,X35)|r1_waybel_7(X33,k2_yellow19(X33,X34),X35)|~m1_subset_1(X35,u1_struct_0(X33))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~r1_waybel_7(X33,k2_yellow19(X33,X34),X35)|r3_waybel_9(X33,X34,X35)|~m1_subset_1(X35,u1_struct_0(X33))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.13/0.39  cnf(c_0_46, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_48, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_34])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))))), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_36, c_0_34])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_37, c_0_34])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_53, plain, ![X19]:(~l1_struct_0(X19)|m1_subset_1(k2_struct_0(X19),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.13/0.39  cnf(c_0_54, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.13/0.39  cnf(c_0_56, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_34]), c_0_34]), c_0_34])).
% 0.13/0.39  cnf(c_0_57, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_58, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_61, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_34]), c_0_34]), c_0_34]), c_0_34])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))), inference(rw,[status(thm)],[c_0_47, c_0_34])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk4_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.13/0.39  cnf(c_0_64, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  fof(c_0_65, plain, ![X18]:(~l1_struct_0(X18)|k2_struct_0(X18)=u1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.39  cnf(c_0_66, plain, (v2_struct_0(X1)|~v1_xboole_0(esk3_1(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (esk3_1(esk4_0)=u1_struct_0(esk4_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0),X1)|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk4_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.13/0.39  cnf(c_0_69, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_34]), c_0_34]), c_0_34]), c_0_34])).
% 0.13/0.39  cnf(c_0_70, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (r1_waybel_7(esk4_0,k2_yellow19(esk4_0,X1),esk6_0)|v2_struct_0(X1)|~r3_waybel_9(esk4_0,X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_30])]), c_0_42])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|r1_waybel_7(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_49]), c_0_62]), c_0_50]), c_0_51])]), c_0_42]), c_0_52]), c_0_41])])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(k2_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_41])]), c_0_42])).
% 0.13/0.39  cnf(c_0_75, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_41])]), c_0_42])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)|v1_xboole_0(k2_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_64]), c_0_41])]), c_0_42])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk4_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_49]), c_0_62]), c_0_50]), c_0_51])]), c_0_52])).
% 0.13/0.39  cnf(c_0_79, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_34]), c_0_34]), c_0_34])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (v4_orders_2(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_41])]), c_0_76])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (l1_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_75]), c_0_41])]), c_0_76])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(k2_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_64]), c_0_41])]), c_0_42])).
% 0.13/0.39  cnf(c_0_84, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|~r1_waybel_7(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk4_0))|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))|~v7_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_75]), c_0_81]), c_0_41])]), c_0_82])])).
% 0.13/0.39  cnf(c_0_88, negated_conjecture, (v7_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_75]), c_0_41])]), c_0_76])).
% 0.13/0.39  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_90, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_84])).
% 0.13/0.39  cnf(c_0_91, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.39  cnf(c_0_92, negated_conjecture, (~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk6_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_75])).
% 0.13/0.39  cnf(c_0_93, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_75]), c_0_41])]), c_0_76])).
% 0.13/0.39  cnf(c_0_94, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.13/0.39  cnf(c_0_95, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.13/0.39  cnf(c_0_96, negated_conjecture, (r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),X1)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~r1_waybel_7(esk4_0,esk5_0,X1)|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_73]), c_0_60]), c_0_30])]), c_0_42])).
% 0.13/0.39  cnf(c_0_97, negated_conjecture, (~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_41])])).
% 0.13/0.39  cnf(c_0_98, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_41]), c_0_95])]), c_0_42])).
% 0.13/0.39  cnf(c_0_99, negated_conjecture, (r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),X1)|v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))|~r1_waybel_7(esk4_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_75]), c_0_88]), c_0_81]), c_0_82]), c_0_41])])).
% 0.13/0.39  cnf(c_0_100, negated_conjecture, (~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98])])).
% 0.13/0.39  cnf(c_0_101, negated_conjecture, (v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_98]), c_0_59])]), c_0_100])).
% 0.13/0.39  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_101]), c_0_41]), c_0_95])]), c_0_42]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 103
% 0.13/0.39  # Proof object clause steps            : 72
% 0.13/0.39  # Proof object formula steps           : 31
% 0.13/0.39  # Proof object conjectures             : 46
% 0.13/0.39  # Proof object clause conjectures      : 43
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 30
% 0.13/0.39  # Proof object initial formulas used   : 15
% 0.13/0.39  # Proof object generating inferences   : 29
% 0.13/0.39  # Proof object simplifying inferences  : 109
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 15
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 41
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 40
% 0.13/0.39  # Processed clauses                    : 178
% 0.13/0.39  # ...of these trivial                  : 4
% 0.13/0.39  # ...subsumed                          : 49
% 0.13/0.39  # ...remaining for further processing  : 125
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 1
% 0.13/0.39  # Backward-rewritten                   : 9
% 0.13/0.39  # Generated clauses                    : 210
% 0.13/0.39  # ...of the previous two non-trivial   : 179
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 206
% 0.13/0.39  # Factorizations                       : 2
% 0.13/0.39  # Equation resolutions                 : 2
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 113
% 0.13/0.39  #    Positive orientable unit clauses  : 27
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 5
% 0.13/0.39  #    Non-unit-clauses                  : 81
% 0.13/0.39  # Current number of unprocessed clauses: 40
% 0.13/0.39  # ...number of literals in the above   : 287
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 11
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 6894
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 874
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 39
% 0.13/0.39  # Unit Clause-clause subsumption calls : 145
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 19
% 0.13/0.39  # BW rewrite match successes           : 4
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 10514
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.044 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.051 s
% 0.13/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
