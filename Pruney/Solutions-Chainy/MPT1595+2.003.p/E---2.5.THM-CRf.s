%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 363 expanded)
%              Number of clauses        :   42 ( 149 expanded)
%              Number of leaves         :   11 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  250 (1221 expanded)
%              Number of equality atoms :   28 ( 217 expanded)
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

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
                <=> r1_tarski(X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow_1])).

fof(c_0_12,plain,(
    ! [X24] :
      ( u1_struct_0(k2_yellow_1(X24)) = X24
      & u1_orders_2(k2_yellow_1(X24)) = k1_yellow_1(X24) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_13,plain,(
    ! [X23] : k1_yellow_1(X23) = k1_wellord2(X23) ),
    inference(variable_rename,[status(thm)],[redefinition_k1_yellow_1])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r3_orders_2(X17,X18,X19)
        | r1_orders_2(X17,X18,X19)
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17)) )
      & ( ~ r1_orders_2(X17,X18,X19)
        | r3_orders_2(X17,X18,X19)
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_15,plain,(
    ! [X21] :
      ( v1_orders_2(k2_yellow_1(X21))
      & v3_orders_2(k2_yellow_1(X21))
      & v4_orders_2(k2_yellow_1(X21))
      & v5_orders_2(k2_yellow_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_16,plain,(
    ! [X20] :
      ( v1_orders_2(k2_yellow_1(X20))
      & l1_orders_2(k2_yellow_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0)))
    & m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0)))
    & ( ~ r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk5_0) )
    & ( r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
      | r1_tarski(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_18,plain,(
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

cnf(c_0_19,plain,
    ( u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_yellow_1(X1) = k1_wellord2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X13] : v1_relat_1(k1_wellord2(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( u1_orders_2(k2_yellow_1(X1)) = k1_wellord2(X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r1_orders_2(X14,X15,X16)
        | r2_hidden(k4_tarski(X15,X16),u1_orders_2(X14))
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),u1_orders_2(X14))
        | r1_orders_2(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_32,plain,(
    ! [X22] :
      ( ( ~ v2_struct_0(k2_yellow_1(X22))
        | v1_xboole_0(X22) )
      & ( v1_orders_2(k2_yellow_1(X22))
        | v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(k2_yellow_1(X1))
    | r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_34,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != u1_orders_2(k2_yellow_1(X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( v1_relat_1(u1_orders_2(k2_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0))
    | r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_44,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X5,X6)
      | v1_xboole_0(X6)
      | r2_hidden(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_45,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_38])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X3 != u1_orders_2(k2_yellow_1(X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_39,c_0_29])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))
    | ~ r1_orders_2(k2_yellow_1(X3),X1,X2)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_25])])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_53,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ r1_tarski(X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_25]),c_0_23]),c_0_23])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_38])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r2_hidden(k4_tarski(esk4_0,esk5_0),u1_orders_2(k2_yellow_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35]),c_0_36])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_35]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_36]),c_0_43])).

cnf(c_0_58,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_tarski(X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(X1),esk4_0,esk5_0)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r2_hidden(esk4_0,X1)
    | ~ m1_subset_1(esk5_0,X1)
    | ~ m1_subset_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_59])])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_57]),c_0_35]),c_0_36])]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_63]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
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
% 0.20/0.38  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.20/0.38  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.20/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3)))))), inference(assume_negation,[status(cth)],[t3_yellow_1])).
% 0.20/0.38  fof(c_0_12, plain, ![X24]:(u1_struct_0(k2_yellow_1(X24))=X24&u1_orders_2(k2_yellow_1(X24))=k1_yellow_1(X24)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.38  fof(c_0_13, plain, ![X23]:k1_yellow_1(X23)=k1_wellord2(X23), inference(variable_rename,[status(thm)],[redefinition_k1_yellow_1])).
% 0.20/0.38  fof(c_0_14, plain, ![X17, X18, X19]:((~r3_orders_2(X17,X18,X19)|r1_orders_2(X17,X18,X19)|(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))))&(~r1_orders_2(X17,X18,X19)|r3_orders_2(X17,X18,X19)|(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X21]:(((v1_orders_2(k2_yellow_1(X21))&v3_orders_2(k2_yellow_1(X21)))&v4_orders_2(k2_yellow_1(X21)))&v5_orders_2(k2_yellow_1(X21))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.38  fof(c_0_16, plain, ![X20]:(v1_orders_2(k2_yellow_1(X20))&l1_orders_2(k2_yellow_1(X20))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.38  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk3_0)&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0)))&(m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0)))&((~r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|~r1_tarski(esk4_0,esk5_0))&(r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|r1_tarski(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.20/0.38  fof(c_0_18, plain, ![X7, X8, X9, X10]:(((k3_relat_1(X8)=X7|X8!=k1_wellord2(X7)|~v1_relat_1(X8))&((~r2_hidden(k4_tarski(X9,X10),X8)|r1_tarski(X9,X10)|(~r2_hidden(X9,X7)|~r2_hidden(X10,X7))|X8!=k1_wellord2(X7)|~v1_relat_1(X8))&(~r1_tarski(X9,X10)|r2_hidden(k4_tarski(X9,X10),X8)|(~r2_hidden(X9,X7)|~r2_hidden(X10,X7))|X8!=k1_wellord2(X7)|~v1_relat_1(X8))))&(((r2_hidden(esk1_2(X7,X8),X7)|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8))&(r2_hidden(esk2_2(X7,X8),X7)|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8)))&((~r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|~r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8))&(r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|r1_tarski(esk1_2(X7,X8),esk2_2(X7,X8))|k3_relat_1(X8)!=X7|X8=k1_wellord2(X7)|~v1_relat_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  cnf(c_0_19, plain, (u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_20, plain, (k1_yellow_1(X1)=k1_wellord2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_21, plain, ![X13]:v1_relat_1(k1_wellord2(X13)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_23, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_24, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_25, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_yellow_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_29, plain, (u1_orders_2(k2_yellow_1(X1))=k1_wellord2(X1)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_30, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  fof(c_0_31, plain, ![X14, X15, X16]:((~r1_orders_2(X14,X15,X16)|r2_hidden(k4_tarski(X15,X16),u1_orders_2(X14))|~m1_subset_1(X16,u1_struct_0(X14))|~m1_subset_1(X15,u1_struct_0(X14))|~l1_orders_2(X14))&(~r2_hidden(k4_tarski(X15,X16),u1_orders_2(X14))|r1_orders_2(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~m1_subset_1(X15,u1_struct_0(X14))|~l1_orders_2(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.20/0.38  fof(c_0_32, plain, ![X22]:((~v2_struct_0(k2_yellow_1(X22))|v1_xboole_0(X22))&(v1_orders_2(k2_yellow_1(X22))|v1_xboole_0(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.20/0.38  cnf(c_0_33, plain, (v2_struct_0(k2_yellow_1(X1))|r1_orders_2(k2_yellow_1(X1),X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_26, c_0_23])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_27, c_0_23])).
% 0.20/0.38  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,X2),X3)|X3!=u1_orders_2(k2_yellow_1(X4))|~v1_relat_1(X3)|~r2_hidden(X2,X4)|~r2_hidden(X1,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_38, plain, (v1_relat_1(u1_orders_2(k2_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.20/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_41, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))|r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_44, plain, ![X5, X6]:(~m1_subset_1(X5,X6)|(v1_xboole_0(X6)|r2_hidden(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.38  cnf(c_0_45, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_46, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_47, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_38])])).
% 0.20/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X3!=u1_orders_2(k2_yellow_1(X4))|~v1_relat_1(X3)|~r2_hidden(X2,X4)|~r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(rw,[status(thm)],[c_0_39, c_0_29])).
% 0.20/0.38  cnf(c_0_49, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))|~r1_orders_2(k2_yellow_1(X3),X1,X2)|~m1_subset_1(X2,X3)|~m1_subset_1(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_25])])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.20/0.38  cnf(c_0_51, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_52, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23]), c_0_24]), c_0_25])])).
% 0.20/0.38  cnf(c_0_53, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|~r1_tarski(X2,X3)|~r2_hidden(X3,X1)|~r2_hidden(X2,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_25]), c_0_23]), c_0_23])])).
% 0.20/0.38  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X3)))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_38])])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r2_hidden(k4_tarski(esk4_0,esk5_0),u1_orders_2(k2_yellow_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35]), c_0_36])])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_35]), c_0_43])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_36]), c_0_43])).
% 0.20/0.38  cnf(c_0_58, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_tarski(X2,X3)|~r2_hidden(X3,X1)|~r2_hidden(X2,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (~r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)|~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (r3_orders_2(k2_yellow_1(X1),esk4_0,esk5_0)|v2_struct_0(k2_yellow_1(X1))|~r2_hidden(esk5_0,X1)|~r2_hidden(esk4_0,X1)|~m1_subset_1(esk5_0,X1)|~m1_subset_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (~r3_orders_2(k2_yellow_1(esk3_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_59])])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_57]), c_0_35]), c_0_36])]), c_0_62])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_63]), c_0_43]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 65
% 0.20/0.38  # Proof object clause steps            : 42
% 0.20/0.38  # Proof object formula steps           : 23
% 0.20/0.38  # Proof object conjectures             : 20
% 0.20/0.38  # Proof object clause conjectures      : 17
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 11
% 0.20/0.38  # Proof object generating inferences   : 14
% 0.20/0.38  # Proof object simplifying inferences  : 44
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 11
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 29
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 27
% 0.20/0.38  # Processed clauses                    : 78
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 74
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 6
% 0.20/0.38  # Generated clauses                    : 36
% 0.20/0.38  # ...of the previous two non-trivial   : 32
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 29
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
% 0.20/0.38  # Current number of processed clauses  : 35
% 0.20/0.38  #    Positive orientable unit clauses  : 14
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 19
% 0.20/0.38  # Current number of unprocessed clauses: 5
% 0.20/0.38  # ...number of literals in the above   : 35
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 34
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 179
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 42
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 24
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 2
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3203
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
