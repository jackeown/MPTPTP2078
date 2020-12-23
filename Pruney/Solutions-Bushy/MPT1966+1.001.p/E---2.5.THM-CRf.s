%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1966+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (14330 expanded)
%              Number of clauses        :  101 (6194 expanded)
%              Number of leaves         :   20 (3839 expanded)
%              Depth                    :   25
%              Number of atoms          :  598 (56530 expanded)
%              Number of equality atoms :   76 (6935 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   53 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_waybel_7,axiom,(
    ! [X1] : u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t15_waybel_7,conjecture,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X2)
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
     => ( v2_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3] :
            ( ( v1_finset_1(X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
           => ( r1_tarski(X3,X2)
             => r2_hidden(k8_setfam_1(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_7)).

fof(t43_waybel_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( ( v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X2)) )
               => ( X3 != k1_xboole_0
                 => r2_hidden(k2_yellow_0(X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_waybel_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(cc8_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_yellow_0(X1)
          & v2_waybel_1(X1)
          & v10_waybel_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(fc1_waybel_7,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v11_waybel_1(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(t20_yellow_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
     => k2_yellow_0(k3_yellow_1(X1),X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t22_waybel_4,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => r2_hidden(k4_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_4)).

fof(t19_yellow_1,axiom,(
    ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(cc7_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v9_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v2_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc7_waybel_1)).

fof(cc10_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v9_waybel_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_waybel_1)).

fof(c_0_20,plain,(
    ! [X29] : u1_struct_0(k3_yellow_1(X29)) = k9_setfam_1(X29) ),
    inference(variable_rename,[status(thm)],[t4_waybel_7])).

fof(c_0_21,plain,(
    ! [X14] : k9_setfam_1(X14) = k1_zfmisc_1(X14) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v1_xboole_0(X2)
          & v13_waybel_0(X2,k3_yellow_1(X1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
       => ( v2_waybel_0(X2,k3_yellow_1(X1))
        <=> ! [X3] :
              ( ( v1_finset_1(X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
             => ( r1_tarski(X3,X2)
               => r2_hidden(k8_setfam_1(X1,X3),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_waybel_7])).

fof(c_0_23,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_waybel_0(X26,X25)
        | ~ v1_finset_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
        | X27 = k1_xboole_0
        | r2_hidden(k2_yellow_0(X25,X27),X26)
        | v1_xboole_0(X26)
        | ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v2_lattice3(X25)
        | ~ l1_orders_2(X25) )
      & ( v1_finset_1(esk1_2(X25,X26))
        | v2_waybel_0(X26,X25)
        | v1_xboole_0(X26)
        | ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v2_lattice3(X25)
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk1_2(X25,X26),k1_zfmisc_1(X26))
        | v2_waybel_0(X26,X25)
        | v1_xboole_0(X26)
        | ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v2_lattice3(X25)
        | ~ l1_orders_2(X25) )
      & ( esk1_2(X25,X26) != k1_xboole_0
        | v2_waybel_0(X26,X25)
        | v1_xboole_0(X26)
        | ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v2_lattice3(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ r2_hidden(k2_yellow_0(X25,esk1_2(X25,X26)),X26)
        | v2_waybel_0(X26,X25)
        | v1_xboole_0(X26)
        | ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v2_lattice3(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_waybel_0])])])])])])).

cnf(c_0_24,plain,
    ( u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,negated_conjecture,(
    ! [X36] :
      ( ~ v1_xboole_0(esk3_0)
      & v13_waybel_0(esk3_0,k3_yellow_1(esk2_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk2_0))))
      & ( v1_finset_1(esk4_0)
        | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
        | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) )
      & ( r1_tarski(esk4_0,esk3_0)
        | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) )
      & ( ~ r2_hidden(k8_setfam_1(esk2_0,esk4_0),esk3_0)
        | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) )
      & ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
        | ~ v1_finset_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
        | ~ r1_tarski(X36,esk3_0)
        | r2_hidden(k8_setfam_1(esk2_0,X36),esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])])])).

fof(c_0_27,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(X2))
    | v2_waybel_0(X2,X1)
    | v1_xboole_0(X2)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( u1_struct_0(k3_yellow_1(X1)) = k1_zfmisc_1(X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X11] :
      ( ~ v2_struct_0(k3_yellow_1(X11))
      & v1_orders_2(k3_yellow_1(X11))
      & v3_orders_2(k3_yellow_1(X11))
      & v4_orders_2(k3_yellow_1(X11))
      & v5_orders_2(k3_yellow_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_32,plain,(
    ! [X9] :
      ( v1_orders_2(k3_yellow_1(X9))
      & l1_orders_2(k3_yellow_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | v2_waybel_0(X2,X1)
    | m1_subset_1(esk1_2(X1,X2),u1_struct_0(k3_yellow_1(X2)))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(esk2_0))))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( v4_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v3_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_42,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v3_orders_2(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v4_orders_2(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v5_orders_2(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v1_lattice3(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v2_lattice3(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v3_yellow_0(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v2_waybel_1(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v10_waybel_1(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

fof(c_0_43,plain,(
    ! [X10] :
      ( v1_orders_2(k3_yellow_1(X10))
      & v11_waybel_1(k3_yellow_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[fc1_waybel_7])).

fof(c_0_44,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | m1_subset_1(esk1_2(k3_yellow_1(esk2_0),esk3_0),u1_struct_0(k3_yellow_1(esk3_0)))
    | ~ v2_lattice3(k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_47,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( v11_waybel_1(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(k3_yellow_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | m1_subset_1(esk1_2(k3_yellow_1(esk2_0),esk3_0),u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_40])]),c_0_49])).

fof(c_0_53,plain,(
    ! [X7,X8] :
      ( ( X8 = k1_xboole_0
        | k8_setfam_1(X7,X8) = k6_setfam_1(X7,X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) )
      & ( X8 != k1_xboole_0
        | k8_setfam_1(X7,X8) = X7
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_54,plain,(
    ! [X30] :
      ( ~ v1_xboole_0(X30)
      | X30 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_55,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | k6_setfam_1(X12,X13) = k1_setfam_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(k3_yellow_1(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | r1_tarski(esk1_2(k3_yellow_1(esk2_0),esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_62,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | r1_tarski(esk1_2(k3_yellow_1(esk2_0),esk3_0),u1_struct_0(k3_yellow_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | k6_setfam_1(X2,X1) = k8_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_29]),c_0_29])).

cnf(c_0_66,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_67,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))
      | k2_yellow_0(k3_yellow_1(X19),X20) = k1_setfam_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t20_yellow_1])])])).

cnf(c_0_68,plain,
    ( v2_waybel_0(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(k2_yellow_0(X1,esk1_2(X1,X2)),X2)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_29]),c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | m1_subset_1(esk1_2(k3_yellow_1(esk2_0),esk3_0),u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( k6_setfam_1(X1,X2) = k8_setfam_1(X1,X2)
    | X2 = o_0_0_xboole_0
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1))))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | k2_yellow_0(k3_yellow_1(X2),X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_73,plain,(
    ! [X31,X32] :
      ( ~ v1_xboole_0(X31)
      | X31 = X32
      | ~ v1_xboole_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_74,plain,
    ( v1_finset_1(esk1_2(X1,X2))
    | v2_waybel_0(X2,X1)
    | v1_xboole_0(X2)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X2)
    | v2_waybel_0(X2,X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ r2_hidden(k2_yellow_0(X1,esk1_2(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk1_2(k3_yellow_1(esk2_0),esk3_0)) = k1_setfam_1(esk1_2(k3_yellow_1(esk2_0),esk3_0))
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk1_2(k3_yellow_1(esk2_0),esk3_0)) = k8_setfam_1(esk2_0,esk1_2(k3_yellow_1(esk2_0),esk3_0))
    | esk1_2(k3_yellow_1(esk2_0),esk3_0) = o_0_0_xboole_0
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_78,plain,
    ( k2_yellow_0(k3_yellow_1(X2),X1) = k1_setfam_1(X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2))))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_29])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X2)
    | v2_waybel_0(X2,X1)
    | v1_finset_1(esk1_2(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1)))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_29])).

cnf(c_0_81,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(esk2_0),esk1_2(k3_yellow_1(esk2_0),esk3_0)),esk3_0)
    | ~ v2_lattice3(k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( k1_setfam_1(esk1_2(k3_yellow_1(esk2_0),esk3_0)) = k8_setfam_1(esk2_0,esk1_2(k3_yellow_1(esk2_0),esk3_0))
    | esk1_2(k3_yellow_1(esk2_0),esk3_0) = o_0_0_xboole_0
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k1_setfam_1(esk1_2(k3_yellow_1(esk2_0),esk3_0)) = k2_yellow_0(k3_yellow_1(esk2_0),esk1_2(k3_yellow_1(esk2_0),esk3_0))
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | v1_xboole_0(esk1_2(k3_yellow_1(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_70])).

cnf(c_0_84,plain,
    ( o_0_0_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_61])).

cnf(c_0_85,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | r2_hidden(k8_setfam_1(esk2_0,X1),esk3_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_86,negated_conjecture,
    ( v1_finset_1(esk1_2(k3_yellow_1(esk2_0),esk3_0))
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | ~ v2_lattice3(k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_87,plain,
    ( v2_waybel_0(X2,X1)
    | v1_xboole_0(X2)
    | esk1_2(X1,X2) != k1_xboole_0
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_88,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(esk2_0),esk1_2(k3_yellow_1(esk2_0),esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_47]),c_0_48]),c_0_40])]),c_0_49])).

cnf(c_0_89,negated_conjecture,
    ( k2_yellow_0(k3_yellow_1(esk2_0),esk1_2(k3_yellow_1(esk2_0),esk3_0)) = k8_setfam_1(esk2_0,esk1_2(k3_yellow_1(esk2_0),esk3_0))
    | esk1_2(k3_yellow_1(esk2_0),esk3_0) = o_0_0_xboole_0
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | r2_hidden(k8_setfam_1(esk2_0,X1),esk3_0)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_29]),c_0_29])).

cnf(c_0_91,negated_conjecture,
    ( v1_finset_1(esk1_2(k3_yellow_1(esk2_0),esk3_0))
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_47]),c_0_48]),c_0_40])]),c_0_49])).

cnf(c_0_92,plain,
    ( v1_xboole_0(X2)
    | v2_waybel_0(X2,X1)
    | esk1_2(X1,X2) != k1_xboole_0
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1)))) ),
    inference(rw,[status(thm)],[c_0_87,c_0_29])).

cnf(c_0_93,negated_conjecture,
    ( esk1_2(k3_yellow_1(esk2_0),esk3_0) = o_0_0_xboole_0
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | ~ r2_hidden(k8_setfam_1(esk2_0,esk1_2(k3_yellow_1(esk2_0),esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k8_setfam_1(esk2_0,esk1_2(k3_yellow_1(esk2_0),esk3_0)),esk3_0)
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_58]),c_0_70]),c_0_91])).

cnf(c_0_95,plain,
    ( v2_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | esk1_2(X2,X1) != o_0_0_xboole_0
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X2))))
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(rw,[status(thm)],[c_0_92,c_0_66])).

cnf(c_0_96,negated_conjecture,
    ( esk1_2(k3_yellow_1(esk2_0),esk3_0) = o_0_0_xboole_0
    | v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | ~ v2_lattice3(k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_36]),c_0_35]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_98,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X2,X3),X1)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ v1_finset_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_100,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_47]),c_0_48]),c_0_40])]),c_0_49])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_102,plain,
    ( X3 = k1_xboole_0
    | v1_xboole_0(X1)
    | r2_hidden(k2_yellow_0(X2,X3),X1)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v1_finset_1(X3)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_29]),c_0_29])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( v1_finset_1(esk4_0)
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(esk2_0)))))
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_29]),c_0_29])).

cnf(c_0_106,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(k2_yellow_0(X2,X1),X3)
    | v1_xboole_0(X3)
    | ~ v1_finset_1(X1)
    | ~ v13_waybel_0(X3,X2)
    | ~ v2_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3)))
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(rw,[status(thm)],[c_0_102,c_0_66])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( v1_finset_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_100])])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_100])])).

fof(c_0_110,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v3_orders_2(X21)
      | ~ v4_orders_2(X21)
      | ~ v5_orders_2(X21)
      | ~ v2_yellow_0(X21)
      | ~ l1_orders_2(X21)
      | v1_xboole_0(X22)
      | ~ v2_waybel_0(X22,X21)
      | ~ v13_waybel_0(X22,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | r2_hidden(k4_yellow_0(X21),X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_waybel_4])])])])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_0),esk3_0)
    | ~ v13_waybel_0(esk3_0,X1)
    | ~ v2_waybel_0(esk3_0,X1)
    | ~ m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])]),c_0_41])).

cnf(c_0_112,negated_conjecture,
    ( ~ r2_hidden(k8_setfam_1(esk2_0,esk4_0),esk3_0)
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_113,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk4_0) = k1_setfam_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_109])).

cnf(c_0_114,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k4_yellow_0(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

fof(c_0_115,plain,(
    ! [X15] : k4_yellow_0(k3_yellow_1(X15)) = X15 ),
    inference(variable_rename,[status(thm)],[t19_yellow_1])).

cnf(c_0_116,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0
    | r2_hidden(k2_yellow_0(k3_yellow_1(esk2_0),esk4_0),esk3_0)
    | ~ v2_lattice3(k3_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_36]),c_0_100]),c_0_35]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_118,negated_conjecture,
    ( ~ r2_hidden(k8_setfam_1(esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_100])])).

cnf(c_0_119,negated_conjecture,
    ( k8_setfam_1(esk2_0,esk4_0) = k1_setfam_1(esk4_0)
    | esk4_0 = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_109]),c_0_113])).

cnf(c_0_120,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k4_yellow_0(X1),X2)
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1)))) ),
    inference(rw,[status(thm)],[c_0_114,c_0_29])).

cnf(c_0_121,plain,
    ( k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

fof(c_0_122,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v9_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v2_yellow_0(X5)
        | v2_struct_0(X5)
        | ~ v9_waybel_1(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc7_waybel_1])])])])).

cnf(c_0_123,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_29]),c_0_29])).

cnf(c_0_124,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0
    | r2_hidden(k2_yellow_0(k3_yellow_1(esk2_0),esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_47]),c_0_48]),c_0_40])]),c_0_49])).

cnf(c_0_125,negated_conjecture,
    ( k2_yellow_0(k3_yellow_1(esk2_0),esk4_0) = k1_setfam_1(esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_109])).

cnf(c_0_126,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0
    | ~ r2_hidden(k1_setfam_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | ~ v2_yellow_0(k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_35]),c_0_121]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41]),c_0_49])).

cnf(c_0_128,plain,
    ( v2_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v9_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

fof(c_0_129,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v9_waybel_1(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_waybel_1])])])])).

cnf(c_0_130,plain,
    ( k8_setfam_1(X1,X2) = X1
    | X2 != o_0_0_xboole_0
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1))))) ),
    inference(rw,[status(thm)],[c_0_123,c_0_66])).

cnf(c_0_131,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_84]),c_0_126])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
    | ~ v9_waybel_1(k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_40])]),c_0_49])).

cnf(c_0_133,plain,
    ( v9_waybel_1(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_134,plain,
    ( k8_setfam_1(X1,o_0_0_xboole_0) = X1
    | ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1))))) ),
    inference(er,[status(thm)],[c_0_130])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(o_0_0_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(esk2_0))))) ),
    inference(rw,[status(thm)],[c_0_109,c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | ~ v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_48]),c_0_40])]),c_0_49])).

cnf(c_0_137,negated_conjecture,
    ( ~ r2_hidden(k8_setfam_1(esk2_0,o_0_0_xboole_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_131])).

cnf(c_0_138,negated_conjecture,
    ( k8_setfam_1(esk2_0,o_0_0_xboole_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_100])])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_138]),c_0_139])]),
    [proof]).

%------------------------------------------------------------------------------
