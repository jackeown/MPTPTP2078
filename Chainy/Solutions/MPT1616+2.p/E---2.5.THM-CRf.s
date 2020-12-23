%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1616+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 10.56s
% Output     : CNFRefutation 10.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of clauses        :   24 (  35 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 396 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d1_pre_topc)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',l49_zfmisc_1)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',d12_setfam_1)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t60_setfam_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',dt_u1_pre_topc)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT025+2.ax',d12_yellow_0)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',redefinition_k5_setfam_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

fof(c_0_12,plain,(
    ! [X5888,X5889,X5890,X5891] :
      ( ( r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | ~ v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( ~ m1_subset_1(X5889,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5888))))
        | ~ r1_tarski(X5889,u1_pre_topc(X5888))
        | r2_hidden(k5_setfam_1(u1_struct_0(X5888),X5889),u1_pre_topc(X5888))
        | ~ v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( ~ m1_subset_1(X5890,k1_zfmisc_1(u1_struct_0(X5888)))
        | ~ m1_subset_1(X5891,k1_zfmisc_1(u1_struct_0(X5888)))
        | ~ r2_hidden(X5890,u1_pre_topc(X5888))
        | ~ r2_hidden(X5891,u1_pre_topc(X5888))
        | r2_hidden(k9_subset_1(u1_struct_0(X5888),X5890,X5891),u1_pre_topc(X5888))
        | ~ v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( m1_subset_1(esk600_1(X5888),k1_zfmisc_1(u1_struct_0(X5888)))
        | m1_subset_1(esk599_1(X5888),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5888))))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( m1_subset_1(esk601_1(X5888),k1_zfmisc_1(u1_struct_0(X5888)))
        | m1_subset_1(esk599_1(X5888),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5888))))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( r2_hidden(esk600_1(X5888),u1_pre_topc(X5888))
        | m1_subset_1(esk599_1(X5888),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5888))))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( r2_hidden(esk601_1(X5888),u1_pre_topc(X5888))
        | m1_subset_1(esk599_1(X5888),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5888))))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X5888),esk600_1(X5888),esk601_1(X5888)),u1_pre_topc(X5888))
        | m1_subset_1(esk599_1(X5888),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5888))))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( m1_subset_1(esk600_1(X5888),k1_zfmisc_1(u1_struct_0(X5888)))
        | r1_tarski(esk599_1(X5888),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( m1_subset_1(esk601_1(X5888),k1_zfmisc_1(u1_struct_0(X5888)))
        | r1_tarski(esk599_1(X5888),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( r2_hidden(esk600_1(X5888),u1_pre_topc(X5888))
        | r1_tarski(esk599_1(X5888),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( r2_hidden(esk601_1(X5888),u1_pre_topc(X5888))
        | r1_tarski(esk599_1(X5888),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X5888),esk600_1(X5888),esk601_1(X5888)),u1_pre_topc(X5888))
        | r1_tarski(esk599_1(X5888),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( m1_subset_1(esk600_1(X5888),k1_zfmisc_1(u1_struct_0(X5888)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5888),esk599_1(X5888)),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( m1_subset_1(esk601_1(X5888),k1_zfmisc_1(u1_struct_0(X5888)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5888),esk599_1(X5888)),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( r2_hidden(esk600_1(X5888),u1_pre_topc(X5888))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5888),esk599_1(X5888)),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( r2_hidden(esk601_1(X5888),u1_pre_topc(X5888))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5888),esk599_1(X5888)),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X5888),esk600_1(X5888),esk601_1(X5888)),u1_pre_topc(X5888))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X5888),esk599_1(X5888)),u1_pre_topc(X5888))
        | ~ r2_hidden(u1_struct_0(X5888),u1_pre_topc(X5888))
        | v2_pre_topc(X5888)
        | ~ l1_pre_topc(X5888) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1124_0)
    & v2_pre_topc(esk1124_0)
    & l1_pre_topc(esk1124_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk1124_0))) != u1_struct_0(esk1124_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X1093,X1094] :
      ( ~ r2_hidden(X1093,X1094)
      | r1_tarski(X1093,k3_tarski(X1094)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_15,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1124_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1124_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X1852,X1853] :
      ( ( ~ m1_setfam_1(X1853,X1852)
        | r1_tarski(X1852,k3_tarski(X1853)) )
      & ( ~ r1_tarski(X1852,k3_tarski(X1853))
        | m1_setfam_1(X1853,X1852) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk1124_0),u1_pre_topc(esk1124_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_21,plain,(
    ! [X2076,X2077] :
      ( ( ~ m1_setfam_1(X2077,X2076)
        | k5_setfam_1(X2076,X2077) = X2076
        | ~ m1_subset_1(X2077,k1_zfmisc_1(k1_zfmisc_1(X2076))) )
      & ( k5_setfam_1(X2076,X2077) != X2076
        | m1_setfam_1(X2077,X2076)
        | ~ m1_subset_1(X2077,k1_zfmisc_1(k1_zfmisc_1(X2076))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_22,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1124_0),k3_tarski(u1_pre_topc(esk1124_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X5922] :
      ( ~ l1_pre_topc(X5922)
      | m1_subset_1(u1_pre_topc(X5922),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5922)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_25,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_setfam_1(u1_pre_topc(esk1124_0),u1_struct_0(esk1124_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X9468] :
      ( ~ l1_orders_2(X9468)
      | k4_yellow_0(X9468) = k2_yellow_0(X9468,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

fof(c_0_29,plain,(
    ! [X9813] :
      ( v1_orders_2(k2_yellow_1(X9813))
      & l1_orders_2(k2_yellow_1(X9813)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_30,plain,(
    ! [X9844] :
      ( v1_xboole_0(X9844)
      | ~ r2_hidden(k3_tarski(X9844),X9844)
      | k4_yellow_0(k2_yellow_1(X9844)) = k3_tarski(X9844) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_31,plain,(
    ! [X389,X390] :
      ( ~ r2_hidden(X389,X390)
      | ~ v1_xboole_0(X390) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_32,plain,(
    ! [X1970,X1971] :
      ( ~ m1_subset_1(X1971,k1_zfmisc_1(k1_zfmisc_1(X1970)))
      | k5_setfam_1(X1970,X1971) = k3_tarski(X1971) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_33,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1124_0),u1_pre_topc(esk1124_0)) = u1_struct_0(esk1124_0)
    | ~ m1_subset_1(u1_pre_topc(esk1124_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1124_0)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1124_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1124_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_35,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1124_0),u1_pre_topc(esk1124_0)) = u1_struct_0(esk1124_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk1124_0))) != u1_struct_0(esk1124_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k2_yellow_0(k2_yellow_1(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk1124_0)) = u1_struct_0(esk1124_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k2_yellow_0(k2_yellow_1(u1_pre_topc(esk1124_0)),k1_xboole_0) != u1_struct_0(esk1124_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42]),c_0_20])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
