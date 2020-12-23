%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:03 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 769 expanded)
%              Number of clauses        :   65 ( 300 expanded)
%              Number of leaves         :   12 ( 196 expanded)
%              Depth                    :   15
%              Number of atoms          :  496 (4034 expanded)
%              Number of equality atoms :   15 ( 278 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | v1_xboole_0(X23)
      | ~ v1_subset_1(X23,u1_struct_0(k3_yellow_1(k2_struct_0(X22))))
      | ~ v2_waybel_0(X23,k3_yellow_1(k2_struct_0(X22)))
      | ~ v13_waybel_0(X23,k3_yellow_1(k2_struct_0(X22)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X22)))))
      | X23 = k2_yellow19(X22,k3_yellow19(X22,k2_struct_0(X22),X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_14,plain,(
    ! [X9] : k3_yellow_1(X9) = k3_lattice3(k1_lattice3(X9)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))
    & v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
      | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0) )
    & ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
      | r2_waybel_7(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
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

fof(c_0_23,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v2_struct_0(k3_yellow19(X16,X17,X18))
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v1_xboole_0(X18)
        | ~ v1_subset_1(X18,u1_struct_0(k3_yellow_1(X17)))
        | ~ v2_waybel_0(X18,k3_yellow_1(X17))
        | ~ v13_waybel_0(X18,k3_yellow_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))) )
      & ( v6_waybel_0(k3_yellow19(X16,X17,X18),X16)
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v1_xboole_0(X18)
        | ~ v1_subset_1(X18,u1_struct_0(k3_yellow_1(X17)))
        | ~ v2_waybel_0(X18,k3_yellow_1(X17))
        | ~ v13_waybel_0(X18,k3_yellow_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))) )
      & ( v7_waybel_0(k3_yellow19(X16,X17,X18))
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v1_xboole_0(X18)
        | ~ v1_subset_1(X18,u1_struct_0(k3_yellow_1(X17)))
        | ~ v2_waybel_0(X18,k3_yellow_1(X17))
        | ~ v13_waybel_0(X18,k3_yellow_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_24,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r2_hidden(X21,k10_yellow_6(X19,X20))
        | r2_waybel_7(X19,k2_yellow19(X19,X20),X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_waybel_7(X19,k2_yellow19(X19,X20),X21)
        | r2_hidden(X21,k10_yellow_6(X19,X20))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).

cnf(c_0_25,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | k2_struct_0(X6) = u1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_34,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v2_struct_0(k3_yellow19(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v1_xboole_0(X15)
        | ~ v2_waybel_0(X15,k3_yellow_1(X14))
        | ~ v13_waybel_0(X15,k3_yellow_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))) )
      & ( v3_orders_2(k3_yellow19(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v1_xboole_0(X15)
        | ~ v2_waybel_0(X15,k3_yellow_1(X14))
        | ~ v13_waybel_0(X15,k3_yellow_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))) )
      & ( v4_orders_2(k3_yellow19(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v1_xboole_0(X15)
        | ~ v2_waybel_0(X15,k3_yellow_1(X14))
        | ~ v13_waybel_0(X15,k3_yellow_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))) )
      & ( v6_waybel_0(k3_yellow19(X13,X14,X15),X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v1_xboole_0(X15)
        | ~ v2_waybel_0(X15,k3_yellow_1(X14))
        | ~ v13_waybel_0(X15,k3_yellow_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_37,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_42,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_45,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v7_waybel_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_47,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_waybel_7(esk1_0,esk2_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])]),c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_26]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_54,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46,c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,X1)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_38]),c_0_39]),c_0_40])]),c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))
    | r2_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_63,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_54]),c_0_40])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57,c_0_54]),c_0_40])])).

cnf(c_0_66,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_26]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59,c_0_60]),c_0_52])])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61,c_0_26]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64])]),c_0_31])).

cnf(c_0_70,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_65,c_0_64]),c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_54]),c_0_40])])).

cnf(c_0_72,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_67,c_0_63]),c_0_64])]),c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68,c_0_54]),c_0_40])])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_71,c_0_64]),c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_72,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_73,c_0_64]),c_0_31])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_76,c_0_75])).

fof(c_0_80,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_77,c_0_79])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_54]),c_0_40])])).

cnf(c_0_85,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_54]),c_0_40])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_84]),c_0_31])).

cnf(c_0_87,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_85]),c_0_31])).

cnf(c_0_88,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88,c_0_43]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.13/0.38  # and selection function NoSelection.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t18_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow19)).
% 0.13/0.38  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.13/0.38  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.38  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.13/0.38  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.13/0.38  fof(t13_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))<=>r2_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow19)).
% 0.13/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.13/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t18_yellow19])).
% 0.13/0.38  fof(c_0_13, plain, ![X22, X23]:(v2_struct_0(X22)|~l1_struct_0(X22)|(v1_xboole_0(X23)|~v1_subset_1(X23,u1_struct_0(k3_yellow_1(k2_struct_0(X22))))|~v2_waybel_0(X23,k3_yellow_1(k2_struct_0(X22)))|~v13_waybel_0(X23,k3_yellow_1(k2_struct_0(X22)))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X22)))))|X23=k2_yellow19(X22,k3_yellow19(X22,k2_struct_0(X22),X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X9]:k3_yellow_1(X9)=k3_lattice3(k1_lattice3(X9)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((((~v1_xboole_0(esk2_0)&v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))&v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&((~r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))|~r2_waybel_7(esk1_0,esk2_0,esk3_0))&(r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))|r2_waybel_7(esk1_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_22, plain, ![X10, X11, X12]:(((~v2_struct_0(k3_yellow19(X10,X11,X12))|(v2_struct_0(X10)|~l1_struct_0(X10)|v1_xboole_0(X11)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|v1_xboole_0(X12)|~v2_waybel_0(X12,k3_yellow_1(X11))|~v13_waybel_0(X12,k3_yellow_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11))))))&(v6_waybel_0(k3_yellow19(X10,X11,X12),X10)|(v2_struct_0(X10)|~l1_struct_0(X10)|v1_xboole_0(X11)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|v1_xboole_0(X12)|~v2_waybel_0(X12,k3_yellow_1(X11))|~v13_waybel_0(X12,k3_yellow_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11)))))))&(l1_waybel_0(k3_yellow19(X10,X11,X12),X10)|(v2_struct_0(X10)|~l1_struct_0(X10)|v1_xboole_0(X11)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|v1_xboole_0(X12)|~v2_waybel_0(X12,k3_yellow_1(X11))|~v13_waybel_0(X12,k3_yellow_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.13/0.38  fof(c_0_23, plain, ![X16, X17, X18]:(((~v2_struct_0(k3_yellow19(X16,X17,X18))|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v1_subset_1(X18,u1_struct_0(k3_yellow_1(X17)))|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17))))))&(v6_waybel_0(k3_yellow19(X16,X17,X18),X16)|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v1_subset_1(X18,u1_struct_0(k3_yellow_1(X17)))|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))))))&(v7_waybel_0(k3_yellow19(X16,X17,X18))|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v1_subset_1(X18,u1_struct_0(k3_yellow_1(X17)))|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.13/0.38  fof(c_0_24, plain, ![X19, X20, X21]:((~r2_hidden(X21,k10_yellow_6(X19,X20))|r2_waybel_7(X19,k2_yellow19(X19,X20),X21)|~m1_subset_1(X21,u1_struct_0(X19))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_waybel_7(X19,k2_yellow19(X19,X20),X21)|r2_hidden(X21,k10_yellow_6(X19,X20))|~m1_subset_1(X21,u1_struct_0(X19))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).
% 0.13/0.38  cnf(c_0_25, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_20, c_0_17])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_32, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_33, plain, ![X6]:(~l1_struct_0(X6)|k2_struct_0(X6)=u1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.38  fof(c_0_34, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_35, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  fof(c_0_36, plain, ![X13, X14, X15]:((((~v2_struct_0(k3_yellow19(X13,X14,X15))|(v2_struct_0(X13)|~l1_struct_0(X13)|v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v1_xboole_0(X15)|~v2_waybel_0(X15,k3_yellow_1(X14))|~v13_waybel_0(X15,k3_yellow_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14))))))&(v3_orders_2(k3_yellow19(X13,X14,X15))|(v2_struct_0(X13)|~l1_struct_0(X13)|v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v1_xboole_0(X15)|~v2_waybel_0(X15,k3_yellow_1(X14))|~v13_waybel_0(X15,k3_yellow_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))))))&(v4_orders_2(k3_yellow19(X13,X14,X15))|(v2_struct_0(X13)|~l1_struct_0(X13)|v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v1_xboole_0(X15)|~v2_waybel_0(X15,k3_yellow_1(X14))|~v13_waybel_0(X15,k3_yellow_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14)))))))&(v6_waybel_0(k3_yellow19(X13,X14,X15),X13)|(v2_struct_0(X13)|~l1_struct_0(X13)|v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v1_xboole_0(X15)|~v2_waybel_0(X15,k3_yellow_1(X14))|~v13_waybel_0(X15,k3_yellow_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X14))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))=esk2_0|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_41, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.38  cnf(c_0_42, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_43, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  fof(c_0_44, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.38  fof(c_0_45, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.38  cnf(c_0_46, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.38  cnf(c_0_47, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_48, plain, (r2_waybel_7(X2,k2_yellow19(X2,X3),X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r2_hidden(X1,k10_yellow_6(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_49, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))|~r2_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r2_waybel_7(esk1_0,esk2_0,X1)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])]), c_0_31])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_26]), c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.38  cnf(c_0_54, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_55, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_56, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46, c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.38  cnf(c_0_58, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,X1)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r2_hidden(X1,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_38]), c_0_39]), c_0_40])]), c_0_31])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk3_0,k10_yellow_6(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)))|r2_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_61, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r2_waybel_7(esk1_0,esk2_0,esk3_0)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_54]), c_0_40])])).
% 0.13/0.38  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57, c_0_54]), c_0_40])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_26]), c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59, c_0_60]), c_0_52])])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61, c_0_26]), c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r2_waybel_7(esk1_0,esk2_0,esk3_0)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64])]), c_0_31])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_65, c_0_64]), c_0_31])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_54]), c_0_40])])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_67, c_0_63]), c_0_64])]), c_0_31])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68, c_0_54]), c_0_40])])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r2_waybel_7(esk1_0,esk2_0,esk3_0)|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_71, c_0_64]), c_0_31])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_72, c_0_70])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|~v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_73, c_0_64]), c_0_31])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r2_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_76, c_0_75])).
% 0.13/0.38  fof(c_0_80, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|~r2_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_77, c_0_79])).
% 0.13/0.38  cnf(c_0_83, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|~r2_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_54]), c_0_40])])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_54]), c_0_40])])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (~r2_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_84]), c_0_31])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, (r2_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_85]), c_0_31])).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_86, c_0_87])).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88, c_0_43]), c_0_40])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 90
% 0.13/0.38  # Proof object clause steps            : 65
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 48
% 0.13/0.38  # Proof object clause conjectures      : 45
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 31
% 0.13/0.38  # Proof object simplifying inferences  : 82
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 30
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 129
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 12
% 0.13/0.38  # ...remaining for further processing  : 117
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 12
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 124
% 0.13/0.38  # ...of the previous two non-trivial   : 119
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 124
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 105
% 0.13/0.38  #    Positive orientable unit clauses  : 12
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 90
% 0.13/0.38  # Current number of unprocessed clauses: 13
% 0.13/0.38  # ...number of literals in the above   : 109
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 14
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 764
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 145
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 24
% 0.13/0.38  # Unit Clause-clause subsumption calls : 60
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 7808
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.043 s
% 0.13/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
