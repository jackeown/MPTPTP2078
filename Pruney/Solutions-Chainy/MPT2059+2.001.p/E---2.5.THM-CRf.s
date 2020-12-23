%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  105 (1938 expanded)
%              Number of clauses        :   72 ( 737 expanded)
%              Number of leaves         :   16 ( 489 expanded)
%              Depth                    :   13
%              Number of atoms          :  504 (11004 expanded)
%              Number of equality atoms :   21 ( 481 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t30_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(c_0_16,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v2_struct_0(k3_yellow19(X32,X33,X34))
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32)
        | v1_xboole_0(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v1_xboole_0(X34)
        | ~ v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))
        | ~ v2_waybel_0(X34,k3_yellow_1(X33))
        | ~ v13_waybel_0(X34,k3_yellow_1(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33)))) )
      & ( v6_waybel_0(k3_yellow19(X32,X33,X34),X32)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32)
        | v1_xboole_0(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v1_xboole_0(X34)
        | ~ v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))
        | ~ v2_waybel_0(X34,k3_yellow_1(X33))
        | ~ v13_waybel_0(X34,k3_yellow_1(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33)))) )
      & ( v7_waybel_0(k3_yellow19(X32,X33,X34))
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32)
        | v1_xboole_0(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v1_xboole_0(X34)
        | ~ v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))
        | ~ v2_waybel_0(X34,k3_yellow_1(X33))
        | ~ v13_waybel_0(X34,k3_yellow_1(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_23,plain,(
    ! [X25] : k3_yellow_1(X25) = k3_lattice3(k1_lattice3(X25)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    & v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ( ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
      | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0) )
    & ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
      | r2_waybel_7(esk3_0,esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | r2_hidden(X24,k1_connsp_2(X23,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | m1_subset_1(k1_connsp_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_30,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v2_struct_0(k3_yellow19(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,k3_yellow_1(X30))
        | ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( v3_orders_2(k3_yellow19(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,k3_yellow_1(X30))
        | ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( v4_orders_2(k3_yellow19(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,k3_yellow_1(X30))
        | ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( v6_waybel_0(k3_yellow19(X29,X30,X31),X29)
        | v2_struct_0(X29)
        | ~ l1_struct_0(X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v1_xboole_0(X31)
        | ~ v2_waybel_0(X31,k3_yellow_1(X30))
        | ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v2_struct_0(k3_yellow19(X26,X27,X28))
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v1_xboole_0(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v1_xboole_0(X28)
        | ~ v2_waybel_0(X28,k3_yellow_1(X27))
        | ~ v13_waybel_0(X28,k3_yellow_1(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27)))) )
      & ( v6_waybel_0(k3_yellow19(X26,X27,X28),X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v1_xboole_0(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v1_xboole_0(X28)
        | ~ v2_waybel_0(X28,k3_yellow_1(X27))
        | ~ v13_waybel_0(X28,k3_yellow_1(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27)))) )
      & ( l1_waybel_0(k3_yellow19(X26,X27,X28),X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v1_xboole_0(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v1_xboole_0(X28)
        | ~ v2_waybel_0(X28,k3_yellow_1(X27))
        | ~ v13_waybel_0(X28,k3_yellow_1(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

fof(c_0_32,plain,(
    ! [X38,X39] :
      ( v2_struct_0(X38)
      | ~ l1_struct_0(X38)
      | v1_xboole_0(X39)
      | ~ v1_subset_1(X39,u1_struct_0(k3_yellow_1(k2_struct_0(X38))))
      | ~ v2_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))
      | ~ v13_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X38)))))
      | X39 = k2_yellow19(X38,k3_yellow19(X38,k2_struct_0(X38),X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_33,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,plain,
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

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_58,plain,(
    ! [X19] :
      ( ~ l1_struct_0(X19)
      | m1_subset_1(k2_struct_0(X19),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk5_0,k1_connsp_2(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk3_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_64,plain,
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

fof(c_0_65,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r2_hidden(X37,k10_yellow_6(X35,X36))
        | r2_waybel_7(X35,k2_yellow19(X35,X36),X37)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_waybel_7(X35,k2_yellow19(X35,X36),X37)
        | r2_hidden(X37,k10_yellow_6(X35,X36))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).

cnf(c_0_66,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56])]),c_0_57])).

cnf(c_0_69,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_70,plain,(
    ! [X18] :
      ( ~ l1_struct_0(X18)
      | k2_struct_0(X18) = u1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(k1_connsp_2(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( k1_connsp_2(esk3_0,esk5_0) = u1_struct_0(esk3_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0))
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_53]),c_0_55]),c_0_56])]),c_0_57])).

cnf(c_0_74,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_53]),c_0_55]),c_0_56])]),c_0_57])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_76,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
    | r2_waybel_7(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_78,negated_conjecture,
    ( k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_53]),c_0_54]),c_0_55]),c_0_56])]),c_0_44]),c_0_57]),c_0_67])])).

cnf(c_0_79,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_67])]),c_0_44])).

cnf(c_0_80,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_69]),c_0_67])]),c_0_44])).

cnf(c_0_83,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_67])]),c_0_44])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_53]),c_0_55]),c_0_56])]),c_0_57])).

cnf(c_0_87,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_42]),c_0_43]),c_0_41])]),c_0_44]),c_0_78])])).

cnf(c_0_88,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_67])]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_80]),c_0_67])]),c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_80]),c_0_67])]),c_0_81])).

cnf(c_0_91,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk3_0)
    | ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_80]),c_0_67])]),c_0_81])).

cnf(c_0_95,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_80]),c_0_88]),c_0_89]),c_0_90]),c_0_67])])).

cnf(c_0_96,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_98,negated_conjecture,
    ( k2_yellow19(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_80]),c_0_67])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_67])])).

cnf(c_0_100,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_67]),c_0_96])]),c_0_44])).

cnf(c_0_101,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))
    | r2_hidden(X1,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)))
    | ~ r2_waybel_7(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_89]),c_0_90]),c_0_42]),c_0_43])]),c_0_44]),c_0_88])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_103,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_100]),c_0_41])]),c_0_102])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_103]),c_0_67]),c_0_96])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.13/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.032 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(t18_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow19)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.13/0.40  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.40  fof(t30_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_hidden(X2,k1_connsp_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.13/0.40  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.13/0.40  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.13/0.40  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.13/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.40  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.13/0.40  fof(t13_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))<=>r2_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow19)).
% 0.13/0.40  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.40  fof(c_0_16, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_17, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t18_yellow19])).
% 0.13/0.40  fof(c_0_19, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  fof(c_0_22, plain, ![X32, X33, X34]:(((~v2_struct_0(k3_yellow19(X32,X33,X34))|(v2_struct_0(X32)|~l1_struct_0(X32)|v1_xboole_0(X33)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|v1_xboole_0(X34)|~v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))|~v2_waybel_0(X34,k3_yellow_1(X33))|~v13_waybel_0(X34,k3_yellow_1(X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33))))))&(v6_waybel_0(k3_yellow19(X32,X33,X34),X32)|(v2_struct_0(X32)|~l1_struct_0(X32)|v1_xboole_0(X33)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|v1_xboole_0(X34)|~v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))|~v2_waybel_0(X34,k3_yellow_1(X33))|~v13_waybel_0(X34,k3_yellow_1(X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33)))))))&(v7_waybel_0(k3_yellow19(X32,X33,X34))|(v2_struct_0(X32)|~l1_struct_0(X32)|v1_xboole_0(X33)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|v1_xboole_0(X34)|~v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))|~v2_waybel_0(X34,k3_yellow_1(X33))|~v13_waybel_0(X34,k3_yellow_1(X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.13/0.40  fof(c_0_23, plain, ![X25]:k3_yellow_1(X25)=k3_lattice3(k1_lattice3(X25)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.40  fof(c_0_24, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((((~v1_xboole_0(esk4_0)&v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))&v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&((~r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|~r2_waybel_7(esk3_0,esk4_0,esk5_0))&(r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|r2_waybel_7(esk3_0,esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.13/0.40  fof(c_0_25, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|r2_hidden(X24,k1_connsp_2(X23,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).
% 0.13/0.40  cnf(c_0_26, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  fof(c_0_28, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  fof(c_0_29, plain, ![X21, X22]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21))|m1_subset_1(k1_connsp_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.13/0.40  fof(c_0_30, plain, ![X29, X30, X31]:((((~v2_struct_0(k3_yellow19(X29,X30,X31))|(v2_struct_0(X29)|~l1_struct_0(X29)|v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|v1_xboole_0(X31)|~v2_waybel_0(X31,k3_yellow_1(X30))|~v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30))))))&(v3_orders_2(k3_yellow19(X29,X30,X31))|(v2_struct_0(X29)|~l1_struct_0(X29)|v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|v1_xboole_0(X31)|~v2_waybel_0(X31,k3_yellow_1(X30))|~v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))))))&(v4_orders_2(k3_yellow19(X29,X30,X31))|(v2_struct_0(X29)|~l1_struct_0(X29)|v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|v1_xboole_0(X31)|~v2_waybel_0(X31,k3_yellow_1(X30))|~v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))))))&(v6_waybel_0(k3_yellow19(X29,X30,X31),X29)|(v2_struct_0(X29)|~l1_struct_0(X29)|v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|v1_xboole_0(X31)|~v2_waybel_0(X31,k3_yellow_1(X30))|~v13_waybel_0(X31,k3_yellow_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.13/0.40  fof(c_0_31, plain, ![X26, X27, X28]:(((~v2_struct_0(k3_yellow19(X26,X27,X28))|(v2_struct_0(X26)|~l1_struct_0(X26)|v1_xboole_0(X27)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|v1_xboole_0(X28)|~v2_waybel_0(X28,k3_yellow_1(X27))|~v13_waybel_0(X28,k3_yellow_1(X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27))))))&(v6_waybel_0(k3_yellow19(X26,X27,X28),X26)|(v2_struct_0(X26)|~l1_struct_0(X26)|v1_xboole_0(X27)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|v1_xboole_0(X28)|~v2_waybel_0(X28,k3_yellow_1(X27))|~v13_waybel_0(X28,k3_yellow_1(X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27)))))))&(l1_waybel_0(k3_yellow19(X26,X27,X28),X26)|(v2_struct_0(X26)|~l1_struct_0(X26)|v1_xboole_0(X27)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|v1_xboole_0(X28)|~v2_waybel_0(X28,k3_yellow_1(X27))|~v13_waybel_0(X28,k3_yellow_1(X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X27))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.13/0.40  fof(c_0_32, plain, ![X38, X39]:(v2_struct_0(X38)|~l1_struct_0(X38)|(v1_xboole_0(X39)|~v1_subset_1(X39,u1_struct_0(k3_yellow_1(k2_struct_0(X38))))|~v2_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))|~v13_waybel_0(X39,k3_yellow_1(k2_struct_0(X38)))|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X38)))))|X39=k2_yellow19(X38,k3_yellow19(X38,k2_struct_0(X38),X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.13/0.40  fof(c_0_33, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.40  cnf(c_0_34, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_35, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_40, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_connsp_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.40  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_47, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_48, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_49, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_50, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_51, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_52, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))))), inference(rw,[status(thm)],[c_0_36, c_0_35])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))), inference(rw,[status(thm)],[c_0_37, c_0_35])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_38, c_0_35])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_39, c_0_35])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  fof(c_0_58, plain, ![X19]:(~l1_struct_0(X19)|m1_subset_1(k2_struct_0(X19),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(esk5_0,k1_connsp_2(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.13/0.40  cnf(c_0_60, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (m1_subset_1(k1_connsp_2(esk3_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.13/0.40  cnf(c_0_62, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_35]), c_0_35]), c_0_35])).
% 0.13/0.40  cnf(c_0_63, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_35]), c_0_35]), c_0_35])).
% 0.13/0.40  cnf(c_0_64, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  fof(c_0_65, plain, ![X35, X36, X37]:((~r2_hidden(X37,k10_yellow_6(X35,X36))|r2_waybel_7(X35,k2_yellow19(X35,X36),X37)|~m1_subset_1(X37,u1_struct_0(X35))|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r2_waybel_7(X35,k2_yellow19(X35,X36),X37)|r2_hidden(X37,k10_yellow_6(X35,X36))|~m1_subset_1(X37,u1_struct_0(X35))|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).
% 0.13/0.40  cnf(c_0_66, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_43])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk3_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_56])]), c_0_57])).
% 0.13/0.40  cnf(c_0_69, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.40  fof(c_0_70, plain, ![X18]:(~l1_struct_0(X18)|k2_struct_0(X18)=u1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (~v1_xboole_0(k1_connsp_2(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_20, c_0_59])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (k1_connsp_2(esk3_0,esk5_0)=u1_struct_0(esk3_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0))|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk3_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_53]), c_0_55]), c_0_56])]), c_0_57])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0),X1)|v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk3_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_53]), c_0_55]), c_0_56])]), c_0_57])).
% 0.13/0.40  cnf(c_0_75, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_35]), c_0_35]), c_0_35])).
% 0.13/0.40  cnf(c_0_76, plain, (r2_waybel_7(X2,k2_yellow19(X2,X3),X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r2_hidden(X1,k10_yellow_6(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.40  cnf(c_0_77, negated_conjecture, (r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|r2_waybel_7(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_53]), c_0_54]), c_0_55]), c_0_56])]), c_0_44]), c_0_57]), c_0_67])])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(k2_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_67])]), c_0_44])).
% 0.13/0.40  cnf(c_0_80, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.40  cnf(c_0_81, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.40  cnf(c_0_82, negated_conjecture, (v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(k2_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_69]), c_0_67])]), c_0_44])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)|v1_xboole_0(k2_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_69]), c_0_67])]), c_0_44])).
% 0.13/0.40  cnf(c_0_84, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_85, negated_conjecture, (~r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_86, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(k2_struct_0(esk3_0))|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk4_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_53]), c_0_55]), c_0_56])]), c_0_57])).
% 0.13/0.40  cnf(c_0_87, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_42]), c_0_43]), c_0_41])]), c_0_44]), c_0_78])])).
% 0.13/0.40  cnf(c_0_88, negated_conjecture, (v7_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_67])]), c_0_81])).
% 0.13/0.40  cnf(c_0_89, negated_conjecture, (v4_orders_2(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_80]), c_0_67])]), c_0_81])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (l1_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_80]), c_0_67])]), c_0_81])).
% 0.13/0.40  cnf(c_0_91, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_92, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_84])).
% 0.13/0.40  cnf(c_0_93, negated_conjecture, (~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~l1_struct_0(esk3_0)|~r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)))), inference(spm,[status(thm)],[c_0_85, c_0_80])).
% 0.13/0.40  cnf(c_0_94, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_80]), c_0_67])]), c_0_81])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_80]), c_0_88]), c_0_89]), c_0_90]), c_0_67])])).
% 0.13/0.40  cnf(c_0_96, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.13/0.40  cnf(c_0_97, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.40  cnf(c_0_98, negated_conjecture, (k2_yellow19(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_80]), c_0_67])])).
% 0.13/0.40  cnf(c_0_99, negated_conjecture, (~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_67])])).
% 0.13/0.40  cnf(c_0_100, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_67]), c_0_96])]), c_0_44])).
% 0.13/0.40  cnf(c_0_101, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))|r2_hidden(X1,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)))|~r2_waybel_7(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_89]), c_0_90]), c_0_42]), c_0_43])]), c_0_44]), c_0_88])])).
% 0.13/0.40  cnf(c_0_102, negated_conjecture, (~r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.13/0.40  cnf(c_0_103, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_100]), c_0_41])]), c_0_102])).
% 0.13/0.40  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_103]), c_0_67]), c_0_96])]), c_0_44]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 105
% 0.13/0.40  # Proof object clause steps            : 72
% 0.13/0.40  # Proof object formula steps           : 33
% 0.13/0.40  # Proof object conjectures             : 46
% 0.13/0.40  # Proof object clause conjectures      : 43
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 30
% 0.13/0.40  # Proof object initial formulas used   : 16
% 0.13/0.40  # Proof object generating inferences   : 30
% 0.13/0.40  # Proof object simplifying inferences  : 113
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 16
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 40
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 39
% 0.13/0.40  # Processed clauses                    : 241
% 0.13/0.40  # ...of these trivial                  : 3
% 0.13/0.40  # ...subsumed                          : 92
% 0.13/0.40  # ...remaining for further processing  : 146
% 0.13/0.40  # Other redundant clauses eliminated   : 2
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 1
% 0.13/0.40  # Backward-rewritten                   : 11
% 0.13/0.40  # Generated clauses                    : 264
% 0.13/0.40  # ...of the previous two non-trivial   : 228
% 0.13/0.40  # Contextual simplify-reflections      : 2
% 0.13/0.40  # Paramodulations                      : 260
% 0.13/0.40  # Factorizations                       : 2
% 0.13/0.40  # Equation resolutions                 : 2
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 132
% 0.13/0.40  #    Positive orientable unit clauses  : 33
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 6
% 0.13/0.40  #    Non-unit-clauses                  : 93
% 0.13/0.40  # Current number of unprocessed clauses: 24
% 0.13/0.40  # ...number of literals in the above   : 173
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 13
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 7162
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 942
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 71
% 0.13/0.40  # Unit Clause-clause subsumption calls : 154
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 19
% 0.13/0.40  # BW rewrite match successes           : 3
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 11928
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.051 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.057 s
% 0.13/0.40  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
