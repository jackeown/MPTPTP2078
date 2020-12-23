%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 393 expanded)
%              Number of clauses        :   44 ( 161 expanded)
%              Number of leaves         :   12 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 (1350 expanded)
%              Number of equality atoms :   28 ( 232 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(redefinition_k1_yellow_1,axiom,(
    ! [X1] : k1_yellow_1(X1) = k1_wellord2(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
                <=> r1_tarski(X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow_1])).

fof(c_0_13,plain,(
    ! [X25] :
      ( u1_struct_0(k2_yellow_1(X25)) = X25
      & u1_orders_2(k2_yellow_1(X25)) = k1_yellow_1(X25) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_14,plain,(
    ! [X24] : k1_yellow_1(X24) = k1_wellord2(X24) ),
    inference(variable_rename,[status(thm)],[redefinition_k1_yellow_1])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r3_orders_2(X19,X20,X21)
        | r1_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) )
      & ( ~ r1_orders_2(X19,X20,X21)
        | r3_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_16,plain,(
    ! [X23] :
      ( v1_orders_2(k2_yellow_1(X23))
      & v3_orders_2(k2_yellow_1(X23))
      & v4_orders_2(k2_yellow_1(X23))
      & v5_orders_2(k2_yellow_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_17,plain,(
    ! [X22] :
      ( v1_orders_2(k2_yellow_1(X22))
      & l1_orders_2(k2_yellow_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0)))
    & m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0)))
    & ( ~ r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk5_0) )
    & ( r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
      | r1_tarski(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_19,plain,(
    ! [X7,X8,X9,X10] :
      ( ( k3_relat_1(X8) = X7
        | X8 != k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X8)
        | r1_tarski(X9,X10)
        | ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X10,X7)
        | X8 != k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r1_tarski(X9,X10)
        | r2_hidden(k4_tarski(X9,X10),X8)
        | ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X10,X7)
        | X8 != k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk2_2(X7,X8),X7)
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | ~ r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))
        | k3_relat_1(X8) != X7
        | X8 = k1_wellord2(X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

cnf(c_0_20,plain,
    ( u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_yellow_1(X1) = k1_wellord2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X13] : v1_relat_1(k1_wellord2(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_23,plain,(
    ! [X14] :
      ( ~ v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_24,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( u1_orders_2(k2_yellow_1(X1)) = k1_wellord2(X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_orders_2(X15,X16,X17)
        | r2_hidden(k4_tarski(X16,X17),u1_orders_2(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),u1_orders_2(X15))
        | r1_orders_2(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_35,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_38,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != u1_orders_2(k2_yellow_1(X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( v1_relat_1(u1_orders_2(k2_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | v2_struct_0(k2_yellow_1(esk3_0))
    | r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_48,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X6,X5)
        | r2_hidden(X6,X5)
        | v1_xboole_0(X5) )
      & ( ~ r2_hidden(X6,X5)
        | m1_subset_1(X6,X5)
        | v1_xboole_0(X5) )
      & ( ~ m1_subset_1(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_xboole_0(X5) )
      & ( ~ v1_xboole_0(X6)
        | m1_subset_1(X6,X5)
        | ~ v1_xboole_0(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_49,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_42])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X3 != u1_orders_2(k2_yellow_1(X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))
    | ~ r1_orders_2(k2_yellow_1(X3),X1,X2)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_28])])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26]),c_0_28])]),c_0_47])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_57,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ r1_tarski(X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_28]),c_0_26]),c_0_26])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_42])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r2_hidden(k4_tarski(esk4_0,esk5_0),u1_orders_2(k2_yellow_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_39]),c_0_40])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_39]),c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_40]),c_0_47])).

cnf(c_0_62,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_tarski(X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(X1),esk4_0,esk5_0)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r2_hidden(esk4_0,X1)
    | ~ m1_subset_1(esk5_0,X1)
    | ~ m1_subset_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_63])])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_60]),c_0_61]),c_0_39]),c_0_40])]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_67]),c_0_26]),c_0_28])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t3_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.38  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.38  fof(redefinition_k1_yellow_1, axiom, ![X1]:k1_yellow_1(X1)=k1_wellord2(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_yellow_1)).
% 0.20/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.38  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.38  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.38  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.20/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.38  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.20/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3)))))), inference(assume_negation,[status(cth)],[t3_yellow_1])).
% 0.20/0.38  fof(c_0_13, plain, ![X25]:(u1_struct_0(k2_yellow_1(X25))=X25&u1_orders_2(k2_yellow_1(X25))=k1_yellow_1(X25)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.38  fof(c_0_14, plain, ![X24]:k1_yellow_1(X24)=k1_wellord2(X24), inference(variable_rename,[status(thm)],[redefinition_k1_yellow_1])).
% 0.20/0.38  fof(c_0_15, plain, ![X19, X20, X21]:((~r3_orders_2(X19,X20,X21)|r1_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))&(~r1_orders_2(X19,X20,X21)|r3_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.38  fof(c_0_16, plain, ![X23]:(((v1_orders_2(k2_yellow_1(X23))&v3_orders_2(k2_yellow_1(X23)))&v4_orders_2(k2_yellow_1(X23)))&v5_orders_2(k2_yellow_1(X23))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.38  fof(c_0_17, plain, ![X22]:(v1_orders_2(k2_yellow_1(X22))&l1_orders_2(k2_yellow_1(X22))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.38  fof(c_0_18, negated_conjecture, (~v1_xboole_0(esk3_0)&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0)))&(m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0)))&((~r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|~r1_tarski(esk4_0,esk5_0))&(r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|r1_tarski(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.20/0.38  fof(c_0_19, plain, ![X7, X8, X9, X10]:(((k3_relat_1(X8)=X7|X8!=k1_wellord2(X7)|~v1_relat_1(X8))&((~r2_hidden(k4_tarski(X9,X10),X8)|r1_tarski(X9,X10)|(~r2_hidden(X9,X7)|~r2_hidden(X10,X7))|X8!=k1_wellord2(X7)|~v1_relat_1(X8))&(~r1_tarski(X9,X10)|r2_hidden(k4_tarski(X9,X10),X8)|(~r2_hidden(X9,X7)|~r2_hidden(X10,X7))|X8!=k1_wellord2(X7)|~v1_relat_1(X8))))&(((r2_hidden(esk1_2(X7,X8),X7)|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8))&(r2_hidden(esk2_2(X7,X8),X7)|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8)))&((~r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|~r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8))&(r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  cnf(c_0_20, plain, (u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, plain, (k1_yellow_1(X1)=k1_wellord2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_22, plain, ![X13]:v1_relat_1(k1_wellord2(X13)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  fof(c_0_23, plain, ![X14]:(~v2_struct_0(X14)|~l1_struct_0(X14)|v1_xboole_0(u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.20/0.38  fof(c_0_24, plain, ![X18]:(~l1_orders_2(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_26, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_27, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_28, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_32, plain, (u1_orders_2(k2_yellow_1(X1))=k1_wellord2(X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_33, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  fof(c_0_34, plain, ![X15, X16, X17]:((~r1_orders_2(X15,X16,X17)|r2_hidden(k4_tarski(X16,X17),u1_orders_2(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|~l1_orders_2(X15))&(~r2_hidden(k4_tarski(X16,X17),u1_orders_2(X15))|r1_orders_2(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|~l1_orders_2(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.20/0.38  cnf(c_0_35, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_37, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_29, c_0_26])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_30, c_0_26])).
% 0.20/0.38  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,X2),X3)|X3!=u1_orders_2(k2_yellow_1(X4))|~v1_relat_1(X3)|~r2_hidden(X2,X4)|~r2_hidden(X1,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_42, plain, (v1_relat_1(u1_orders_2(k2_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.20/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_45, plain, (v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)|~v2_struct_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|v2_struct_0(k2_yellow_1(esk3_0))|r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_48, plain, ![X5, X6]:(((~m1_subset_1(X6,X5)|r2_hidden(X6,X5)|v1_xboole_0(X5))&(~r2_hidden(X6,X5)|m1_subset_1(X6,X5)|v1_xboole_0(X5)))&((~m1_subset_1(X6,X5)|v1_xboole_0(X6)|~v1_xboole_0(X5))&(~v1_xboole_0(X6)|m1_subset_1(X6,X5)|~v1_xboole_0(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.38  cnf(c_0_49, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_50, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_51, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_42])])).
% 0.20/0.38  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X3!=u1_orders_2(k2_yellow_1(X4))|~v1_relat_1(X3)|~r2_hidden(X2,X4)|~r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(rw,[status(thm)],[c_0_43, c_0_32])).
% 0.20/0.38  cnf(c_0_53, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))|~r1_orders_2(k2_yellow_1(X3),X1,X2)|~m1_subset_1(X2,X3)|~m1_subset_1(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_26]), c_0_28])])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26]), c_0_28])]), c_0_47])).
% 0.20/0.38  cnf(c_0_55, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_56, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_26]), c_0_27]), c_0_28])])).
% 0.20/0.38  cnf(c_0_57, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|~r1_tarski(X2,X3)|~r2_hidden(X3,X1)|~r2_hidden(X2,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_28]), c_0_26]), c_0_26])])).
% 0.20/0.38  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_42])])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r2_hidden(k4_tarski(esk4_0,esk5_0),u1_orders_2(k2_yellow_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_39]), c_0_40])])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_39]), c_0_47])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_40]), c_0_47])).
% 0.20/0.38  cnf(c_0_62, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_tarski(X2,X3)|~r2_hidden(X3,X1)|~r2_hidden(X2,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61])])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (~r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (r3_orders_2(k2_yellow_1(X1),esk4_0,esk5_0)|v2_struct_0(k2_yellow_1(X1))|~r2_hidden(esk5_0,X1)|~r2_hidden(esk4_0,X1)|~m1_subset_1(esk5_0,X1)|~m1_subset_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (~r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_63])])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_60]), c_0_61]), c_0_39]), c_0_40])]), c_0_66])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_67]), c_0_26]), c_0_28])]), c_0_47]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 69
% 0.20/0.38  # Proof object clause steps            : 44
% 0.20/0.38  # Proof object formula steps           : 25
% 0.20/0.38  # Proof object conjectures             : 20
% 0.20/0.38  # Proof object clause conjectures      : 17
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 12
% 0.20/0.38  # Proof object generating inferences   : 15
% 0.20/0.38  # Proof object simplifying inferences  : 50
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 12
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 32
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 30
% 0.20/0.38  # Processed clauses                    : 93
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 4
% 0.20/0.38  # ...remaining for further processing  : 88
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 6
% 0.20/0.38  # Generated clauses                    : 49
% 0.20/0.38  # ...of the previous two non-trivial   : 42
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 42
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 7
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 45
% 0.20/0.38  #    Positive orientable unit clauses  : 14
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 29
% 0.20/0.38  # Current number of unprocessed clauses: 6
% 0.20/0.38  # ...number of literals in the above   : 41
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 38
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 413
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 141
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 19
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 2
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3710
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.033 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
