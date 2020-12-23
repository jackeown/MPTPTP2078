%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:00 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 951 expanded)
%              Number of clauses        :   81 ( 371 expanded)
%              Number of leaves         :   16 ( 243 expanded)
%              Depth                    :   19
%              Number of atoms          :  599 (4929 expanded)
%              Number of equality atoms :   15 ( 324 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

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

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X37,X38] :
      ( v2_struct_0(X37)
      | ~ l1_struct_0(X37)
      | v1_xboole_0(X38)
      | ~ v1_subset_1(X38,u1_struct_0(k3_yellow_1(k2_struct_0(X37))))
      | ~ v2_waybel_0(X38,k3_yellow_1(k2_struct_0(X37)))
      | ~ v13_waybel_0(X38,k3_yellow_1(k2_struct_0(X37)))
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X37)))))
      | X38 = k2_yellow19(X37,k3_yellow19(X37,k2_struct_0(X37),X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_18,plain,(
    ! [X24] : k3_yellow_1(X24) = k3_lattice3(k1_lattice3(X24)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_19,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r3_waybel_9(X34,X35,X36)
        | r1_waybel_7(X34,k2_yellow19(X34,X35),X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r1_waybel_7(X34,k2_yellow19(X34,X35),X36)
        | r3_waybel_9(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_27,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_34,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | k2_struct_0(X20) = u1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_35,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_36,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) = esk5_0
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_40,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_struct_0(k3_yellow19(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v1_xboole_0(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v1_xboole_0(X27)
        | ~ v2_waybel_0(X27,k3_yellow_1(X26))
        | ~ v13_waybel_0(X27,k3_yellow_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X26)))) )
      & ( v6_waybel_0(k3_yellow19(X25,X26,X27),X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v1_xboole_0(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v1_xboole_0(X27)
        | ~ v2_waybel_0(X27,k3_yellow_1(X26))
        | ~ v13_waybel_0(X27,k3_yellow_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X26)))) )
      & ( l1_waybel_0(k3_yellow19(X25,X26,X27),X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v1_xboole_0(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v1_xboole_0(X27)
        | ~ v2_waybel_0(X27,k3_yellow_1(X26))
        | ~ v13_waybel_0(X27,k3_yellow_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X26)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,X1)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),X1)
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)
    | r1_waybel_7(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_48,plain,(
    ! [X17] : m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_49,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_50,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk4_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28,c_0_50]),c_0_39])])).

fof(c_0_59,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v2_struct_0(k3_yellow19(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v1_xboole_0(X33)
        | ~ v1_subset_1(X33,u1_struct_0(k3_yellow_1(X32)))
        | ~ v2_waybel_0(X33,k3_yellow_1(X32))
        | ~ v13_waybel_0(X33,k3_yellow_1(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32)))) )
      & ( v6_waybel_0(k3_yellow19(X31,X32,X33),X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v1_xboole_0(X33)
        | ~ v1_subset_1(X33,u1_struct_0(k3_yellow_1(X32)))
        | ~ v2_waybel_0(X33,k3_yellow_1(X32))
        | ~ v13_waybel_0(X33,k3_yellow_1(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32)))) )
      & ( v7_waybel_0(k3_yellow19(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v1_xboole_0(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v1_xboole_0(X33)
        | ~ v1_subset_1(X33,u1_struct_0(k3_yellow_1(X32)))
        | ~ v2_waybel_0(X33,k3_yellow_1(X32))
        | ~ v13_waybel_0(X33,k3_yellow_1(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),X1)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_37]),c_0_38]),c_0_39])]),c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52,c_0_50]),c_0_39])])).

cnf(c_0_63,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2)))) ),
    inference(pm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_50]),c_0_39])])).

cnf(c_0_65,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31,c_0_50]),c_0_39])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk4_0))))) ),
    inference(pm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60,c_0_61]),c_0_45])])).

fof(c_0_70,plain,(
    ! [X28,X29,X30] :
      ( ( ~ v2_struct_0(k3_yellow19(X28,X29,X30))
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v1_xboole_0(X30)
        | ~ v2_waybel_0(X30,k3_yellow_1(X29))
        | ~ v13_waybel_0(X30,k3_yellow_1(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29)))) )
      & ( v3_orders_2(k3_yellow19(X28,X29,X30))
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v1_xboole_0(X30)
        | ~ v2_waybel_0(X30,k3_yellow_1(X29))
        | ~ v13_waybel_0(X30,k3_yellow_1(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29)))) )
      & ( v4_orders_2(k3_yellow19(X28,X29,X30))
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v1_xboole_0(X30)
        | ~ v2_waybel_0(X30,k3_yellow_1(X29))
        | ~ v13_waybel_0(X30,k3_yellow_1(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29)))) )
      & ( v6_waybel_0(k3_yellow19(X28,X29,X30),X28)
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v1_xboole_0(X30)
        | ~ v2_waybel_0(X30,k3_yellow_1(X29))
        | ~ v13_waybel_0(X30,k3_yellow_1(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_71,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67])]),c_0_32]),c_0_33])).

cnf(c_0_72,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_21]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_29,c_0_50]),c_0_39])])).

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_50]),c_0_39])])).

cnf(c_0_75,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v7_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71,c_0_50]),c_0_39])])).

cnf(c_0_77,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_58]),c_0_73]),c_0_64]),c_0_65])]),c_0_33])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74,c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67])]),c_0_32]),c_0_33])).

cnf(c_0_80,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_33])).

cnf(c_0_81,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_82,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_77]),c_0_66])]),c_0_32])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_79,c_0_80]),c_0_32])).

cnf(c_0_85,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_28]),c_0_30]),c_0_31])]),c_0_33])).

cnf(c_0_86,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_50]),c_0_39])])).

cnf(c_0_87,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_58]),c_0_64]),c_0_65])]),c_0_33])).

fof(c_0_88,plain,(
    ! [X22] :
      ( ( m1_subset_1(esk3_1(X22),k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ v1_xboole_0(esk3_1(X22))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( v4_pre_topc(esk3_1(X22),X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_28]),c_0_30]),c_0_31])]),c_0_33])).

cnf(c_0_90,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(k2_struct_0(esk4_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_84,c_0_85]),c_0_32])).

cnf(c_0_91,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_87]),c_0_66])]),c_0_32])).

fof(c_0_92,plain,(
    ! [X14,X15] :
      ( v1_xboole_0(X15)
      | ~ r1_tarski(X15,X14)
      | ~ r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_93,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_94,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_95,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk2_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_89,c_0_90]),c_0_32])).

cnf(c_0_97,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_58]),c_0_64]),c_0_65])]),c_0_33])).

cnf(c_0_98,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91,c_0_50]),c_0_39])])).

cnf(c_0_99,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_100,plain,
    ( v2_struct_0(X1)
    | r1_tarski(esk3_1(X1),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_57,c_0_93])).

cnf(c_0_101,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_102,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96,c_0_50]),c_0_66]),c_0_39])])).

cnf(c_0_104,negated_conjecture,
    ( r1_waybel_7(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97,c_0_98]),c_0_66])]),c_0_32])).

cnf(c_0_105,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(esk3_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(esk3_1(X1),u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk3_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_109,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(esk3_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107,c_0_50]),c_0_39])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_xboole_0(esk3_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_108]),c_0_38]),c_0_39])])).

cnf(c_0_112,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109,c_0_110]),c_0_38]),c_0_39])]),c_0_32]),c_0_111])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112,c_0_42]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:24:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.12/0.38  # and selection function NoSelection.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.030 s
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 0.12/0.38  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.12/0.38  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.12/0.38  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 0.12/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.12/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.38  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.12/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.12/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.38  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.12/0.38  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.12/0.38  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.12/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.12/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.12/0.38  fof(c_0_17, plain, ![X37, X38]:(v2_struct_0(X37)|~l1_struct_0(X37)|(v1_xboole_0(X38)|~v1_subset_1(X38,u1_struct_0(k3_yellow_1(k2_struct_0(X37))))|~v2_waybel_0(X38,k3_yellow_1(k2_struct_0(X37)))|~v13_waybel_0(X38,k3_yellow_1(k2_struct_0(X37)))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X37)))))|X38=k2_yellow19(X37,k3_yellow19(X37,k2_struct_0(X37),X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.12/0.38  fof(c_0_18, plain, ![X24]:k3_yellow_1(X24)=k3_lattice3(k1_lattice3(X24)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.12/0.38  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((((~v1_xboole_0(esk5_0)&v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))&v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|~r1_waybel_7(esk4_0,esk5_0,esk6_0))&(r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|r1_waybel_7(esk4_0,esk5_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.12/0.38  cnf(c_0_20, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_21, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_26, plain, ![X34, X35, X36]:((~r3_waybel_9(X34,X35,X36)|r1_waybel_7(X34,k2_yellow19(X34,X35),X36)|~m1_subset_1(X36,u1_struct_0(X34))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~r1_waybel_7(X34,k2_yellow19(X34,X35),X36)|r3_waybel_9(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.12/0.38  cnf(c_0_27, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))), inference(rw,[status(thm)],[c_0_23, c_0_21])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_24, c_0_21])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_25, c_0_21])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_34, plain, ![X20]:(~l1_struct_0(X20)|k2_struct_0(X20)=u1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.12/0.38  fof(c_0_35, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.38  cnf(c_0_36, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))=esk5_0|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32]), c_0_33])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_40, plain, ![X25, X26, X27]:(((~v2_struct_0(k3_yellow19(X25,X26,X27))|(v2_struct_0(X25)|~l1_struct_0(X25)|v1_xboole_0(X26)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v1_xboole_0(X27)|~v2_waybel_0(X27,k3_yellow_1(X26))|~v13_waybel_0(X27,k3_yellow_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X26))))))&(v6_waybel_0(k3_yellow19(X25,X26,X27),X25)|(v2_struct_0(X25)|~l1_struct_0(X25)|v1_xboole_0(X26)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v1_xboole_0(X27)|~v2_waybel_0(X27,k3_yellow_1(X26))|~v13_waybel_0(X27,k3_yellow_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X26)))))))&(l1_waybel_0(k3_yellow19(X25,X26,X27),X25)|(v2_struct_0(X25)|~l1_struct_0(X25)|v1_xboole_0(X26)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v1_xboole_0(X27)|~v2_waybel_0(X27,k3_yellow_1(X26))|~v13_waybel_0(X27,k3_yellow_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X26))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.12/0.38  cnf(c_0_41, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,X1)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),X1)|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])]), c_0_32])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|r1_waybel_7(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_46, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  fof(c_0_47, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.38  fof(c_0_48, plain, ![X17]:m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.12/0.38  fof(c_0_49, plain, ![X16]:k2_subset_1(X16)=X16, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.38  cnf(c_0_50, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.38  cnf(c_0_51, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.12/0.38  cnf(c_0_53, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.38  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.38  cnf(c_0_55, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_56, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.38  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk4_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28, c_0_50]), c_0_39])])).
% 0.12/0.38  fof(c_0_59, plain, ![X31, X32, X33]:(((~v2_struct_0(k3_yellow19(X31,X32,X33))|(v2_struct_0(X31)|~l1_struct_0(X31)|v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|v1_xboole_0(X33)|~v1_subset_1(X33,u1_struct_0(k3_yellow_1(X32)))|~v2_waybel_0(X33,k3_yellow_1(X32))|~v13_waybel_0(X33,k3_yellow_1(X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32))))))&(v6_waybel_0(k3_yellow19(X31,X32,X33),X31)|(v2_struct_0(X31)|~l1_struct_0(X31)|v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|v1_xboole_0(X33)|~v1_subset_1(X33,u1_struct_0(k3_yellow_1(X32)))|~v2_waybel_0(X33,k3_yellow_1(X32))|~v13_waybel_0(X33,k3_yellow_1(X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32)))))))&(v7_waybel_0(k3_yellow19(X31,X32,X33))|(v2_struct_0(X31)|~l1_struct_0(X31)|v1_xboole_0(X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|v1_xboole_0(X33)|~v1_subset_1(X33,u1_struct_0(k3_yellow_1(X32)))|~v2_waybel_0(X33,k3_yellow_1(X32))|~v13_waybel_0(X33,k3_yellow_1(X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X32))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (~r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk6_0)|~r1_waybel_7(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (r3_waybel_9(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),X1)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~r1_waybel_7(esk4_0,esk5_0,X1)|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_37]), c_0_38]), c_0_39])]), c_0_32])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_63, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))), inference(pm,[status(thm)],[c_0_53, c_0_54])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk4_0)))))), inference(pm,[status(thm)],[c_0_57, c_0_58])).
% 0.12/0.38  cnf(c_0_68, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60, c_0_61]), c_0_45])])).
% 0.12/0.38  fof(c_0_70, plain, ![X28, X29, X30]:((((~v2_struct_0(k3_yellow19(X28,X29,X30))|(v2_struct_0(X28)|~l1_struct_0(X28)|v1_xboole_0(X29)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|v1_xboole_0(X30)|~v2_waybel_0(X30,k3_yellow_1(X29))|~v13_waybel_0(X30,k3_yellow_1(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29))))))&(v3_orders_2(k3_yellow19(X28,X29,X30))|(v2_struct_0(X28)|~l1_struct_0(X28)|v1_xboole_0(X29)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|v1_xboole_0(X30)|~v2_waybel_0(X30,k3_yellow_1(X29))|~v13_waybel_0(X30,k3_yellow_1(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29)))))))&(v4_orders_2(k3_yellow19(X28,X29,X30))|(v2_struct_0(X28)|~l1_struct_0(X28)|v1_xboole_0(X29)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|v1_xboole_0(X30)|~v2_waybel_0(X30,k3_yellow_1(X29))|~v13_waybel_0(X30,k3_yellow_1(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29)))))))&(v6_waybel_0(k3_yellow19(X28,X29,X30),X28)|(v2_struct_0(X28)|~l1_struct_0(X28)|v1_xboole_0(X29)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|v1_xboole_0(X30)|~v2_waybel_0(X30,k3_yellow_1(X29))|~v13_waybel_0(X30,k3_yellow_1(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X29))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67])]), c_0_32]), c_0_33])).
% 0.12/0.38  cnf(c_0_72, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_21]), c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk4_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_29, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0),esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_75, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v7_waybel_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_58]), c_0_73]), c_0_64]), c_0_65])]), c_0_33])).
% 0.12/0.38  cnf(c_0_78, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_79, negated_conjecture, (v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~v7_waybel_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74, c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67])]), c_0_32]), c_0_33])).
% 0.12/0.38  cnf(c_0_80, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk4_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_33])).
% 0.12/0.38  cnf(c_0_81, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.38  cnf(c_0_82, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_77]), c_0_66])]), c_0_32])).
% 0.12/0.38  cnf(c_0_83, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.38  cnf(c_0_84, negated_conjecture, (v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(k2_struct_0(esk4_0))|~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~v4_orders_2(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|~l1_struct_0(esk4_0)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_79, c_0_80]), c_0_32])).
% 0.12/0.38  cnf(c_0_85, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk4_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_28]), c_0_30]), c_0_31])]), c_0_33])).
% 0.12/0.38  cnf(c_0_86, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v4_orders_2(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_87, negated_conjecture, (v4_orders_2(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_58]), c_0_64]), c_0_65])]), c_0_33])).
% 0.12/0.38  fof(c_0_88, plain, ![X22]:(((m1_subset_1(esk3_1(X22),k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~v1_xboole_0(esk3_1(X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))))&(v4_pre_topc(esk3_1(X22),X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.12/0.38  cnf(c_0_89, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk4_0))|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk4_0),esk5_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_28]), c_0_30]), c_0_31])]), c_0_33])).
% 0.12/0.38  cnf(c_0_90, negated_conjecture, (v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(k2_struct_0(esk4_0))|~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~l1_struct_0(esk4_0)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_84, c_0_85]), c_0_32])).
% 0.12/0.38  cnf(c_0_91, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_87]), c_0_66])]), c_0_32])).
% 0.12/0.38  fof(c_0_92, plain, ![X14, X15]:(v1_xboole_0(X15)|(~r1_tarski(X15,X14)|~r1_xboole_0(X15,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.38  cnf(c_0_93, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.12/0.38  fof(c_0_94, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.38  fof(c_0_95, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk2_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk2_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.12/0.38  cnf(c_0_96, negated_conjecture, (v1_xboole_0(k2_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~l1_struct_0(esk4_0)|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_89, c_0_90]), c_0_32])).
% 0.12/0.38  cnf(c_0_97, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk4_0))|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk4_0),esk5_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_58]), c_0_64]), c_0_65])]), c_0_33])).
% 0.12/0.38  cnf(c_0_98, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v2_struct_0(k3_yellow19(esk4_0,u1_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_99, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.12/0.38  cnf(c_0_100, plain, (v2_struct_0(X1)|r1_tarski(esk3_1(X1),u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_57, c_0_93])).
% 0.12/0.38  cnf(c_0_101, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.12/0.38  cnf(c_0_102, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.12/0.38  cnf(c_0_103, negated_conjecture, (v1_xboole_0(k2_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|~r1_waybel_7(esk4_0,esk5_0,esk6_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96, c_0_50]), c_0_66]), c_0_39])])).
% 0.12/0.38  cnf(c_0_104, negated_conjecture, (r1_waybel_7(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97, c_0_98]), c_0_66])]), c_0_32])).
% 0.12/0.38  cnf(c_0_105, plain, (v2_struct_0(X1)|v1_xboole_0(esk3_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r1_xboole_0(esk3_1(X1),u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_99, c_0_100])).
% 0.12/0.38  cnf(c_0_106, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_101, c_0_102])).
% 0.12/0.38  cnf(c_0_107, negated_conjecture, (v1_xboole_0(k2_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(pm,[status(thm)],[c_0_103, c_0_104])).
% 0.12/0.38  cnf(c_0_108, plain, (v2_struct_0(X1)|~v1_xboole_0(esk3_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.12/0.38  cnf(c_0_109, plain, (v2_struct_0(X1)|v1_xboole_0(esk3_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_105, c_0_106])).
% 0.12/0.38  cnf(c_0_110, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107, c_0_50]), c_0_39])])).
% 0.12/0.38  cnf(c_0_111, negated_conjecture, (~v1_xboole_0(esk3_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_108]), c_0_38]), c_0_39])])).
% 0.12/0.38  cnf(c_0_112, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109, c_0_110]), c_0_38]), c_0_39])]), c_0_32]), c_0_111])).
% 0.12/0.38  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112, c_0_42]), c_0_39])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 114
% 0.12/0.38  # Proof object clause steps            : 81
% 0.12/0.38  # Proof object formula steps           : 33
% 0.12/0.38  # Proof object conjectures             : 53
% 0.12/0.38  # Proof object clause conjectures      : 50
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 30
% 0.12/0.38  # Proof object initial formulas used   : 16
% 0.12/0.38  # Proof object generating inferences   : 41
% 0.12/0.38  # Proof object simplifying inferences  : 125
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 16
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 40
% 0.12/0.38  # Removed in clause preprocessing      : 2
% 0.12/0.38  # Initial clauses in saturation        : 38
% 0.12/0.38  # Processed clauses                    : 201
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 62
% 0.12/0.38  # ...remaining for further processing  : 138
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 21
% 0.12/0.38  # Backward-rewritten                   : 0
% 0.12/0.38  # Generated clauses                    : 225
% 0.12/0.38  # ...of the previous two non-trivial   : 212
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 225
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 117
% 0.12/0.38  #    Positive orientable unit clauses  : 15
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 9
% 0.12/0.38  #    Non-unit-clauses                  : 93
% 0.12/0.38  # Current number of unprocessed clauses: 38
% 0.12/0.38  # ...number of literals in the above   : 376
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 23
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 2652
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 286
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 76
% 0.12/0.38  # Unit Clause-clause subsumption calls : 74
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 6
% 0.12/0.38  # BW rewrite match successes           : 0
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 9148
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.039 s
% 0.12/0.38  # System time              : 0.008 s
% 0.12/0.38  # Total time               : 0.047 s
% 0.12/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
