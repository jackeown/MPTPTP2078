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
% DateTime   : Thu Dec  3 11:15:44 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 (3130 expanded)
%              Number of clauses        :   69 (1208 expanded)
%              Number of leaves         :   14 ( 858 expanded)
%              Depth                    :   21
%              Number of atoms          :  355 (10231 expanded)
%              Number of equality atoms :   44 (1705 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v2_lattice3(k2_yellow_1(X1))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(t25_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k12_lattice3(X1,X2,X3)
              <=> r3_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(t16_lattice3,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( v4_orders_2(X1)
                   => k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).

fof(t15_lattice3,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

fof(c_0_15,plain,(
    ! [X10,X11,X12] :
      ( v2_struct_0(X10)
      | ~ v3_orders_2(X10)
      | ~ l1_orders_2(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | r3_orders_2(X10,X11,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_16,plain,(
    ! [X32] :
      ( u1_struct_0(k2_yellow_1(X32)) = X32
      & u1_orders_2(k2_yellow_1(X32)) = k1_yellow_1(X32) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_17,plain,(
    ! [X30] :
      ( v1_orders_2(k2_yellow_1(X30))
      & l1_orders_2(k2_yellow_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_18,plain,(
    ! [X31] :
      ( v1_orders_2(k2_yellow_1(X31))
      & v3_orders_2(k2_yellow_1(X31))
      & v4_orders_2(k2_yellow_1(X31))
      & v5_orders_2(k2_yellow_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v2_lattice3(k2_yellow_1(esk1_0))
    & m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X2)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X17,X18,X19] :
      ( ~ v5_orders_2(X17)
      | ~ v2_lattice3(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k12_lattice3(X17,X18,X19) = k11_lattice3(X17,X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_29,plain,(
    ! [X27,X28,X29] :
      ( ( X28 != k12_lattice3(X27,X28,X29)
        | r3_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v3_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ r3_orders_2(X27,X28,X29)
        | X28 = k12_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v3_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).

fof(c_0_30,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | ~ v2_lattice3(X13)
      | ~ v2_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_31,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,X1)
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_21])).

fof(c_0_33,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r3_orders_2(k2_yellow_1(X33),X34,X35)
        | r1_tarski(X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))
        | v1_xboole_0(X33) )
      & ( ~ r1_tarski(X34,X35)
        | r3_orders_2(k2_yellow_1(X33),X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))
        | v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_34,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k11_lattice3(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_35,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ v5_orders_2(X23)
      | ~ v2_lattice3(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ v4_orders_2(X23)
      | k11_lattice3(X23,k11_lattice3(X23,X24,X25),X26) = k11_lattice3(X23,X24,k11_lattice3(X23,X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).

cnf(c_0_36,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( X2 = k12_lattice3(X1,X2,X3)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_41,plain,(
    ! [X20,X21,X22] :
      ( ~ v5_orders_2(X20)
      | ~ v2_lattice3(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | k11_lattice3(X20,X21,X22) = k11_lattice3(X20,X22,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

cnf(c_0_42,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_43,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_22])])).

cnf(c_0_48,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_42]),c_0_40]),c_0_22])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_21]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_40]),c_0_21]),c_0_32]),c_0_22]),c_0_23])])).

cnf(c_0_55,plain,
    ( v4_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) = k11_lattice3(X1,k11_lattice3(X1,X3,X4),X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_50]),c_0_48]),c_0_40]),c_0_21]),c_0_26]),c_0_22]),c_0_23])])).

cnf(c_0_58,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0),esk1_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_21]),c_0_55]),c_0_48]),c_0_40]),c_0_21]),c_0_32]),c_0_21]),c_0_22])])).

cnf(c_0_60,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0) = k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_48]),c_0_40]),c_0_21]),c_0_21]),c_0_26]),c_0_22])])).

cnf(c_0_61,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_62,plain,
    ( r3_orders_2(X2,X1,X3)
    | X1 != k12_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0) = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_58]),c_0_48]),c_0_40]),c_0_21]),c_0_26]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_26]),c_0_32])])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_21]),c_0_21])).

cnf(c_0_66,plain,
    ( r3_orders_2(X1,X2,X3)
    | k11_lattice3(X1,X2,X3) != X2
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_63]),c_0_48]),c_0_40]),c_0_21]),c_0_26]),c_0_21]),c_0_22])])).

cnf(c_0_68,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_64])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | k11_lattice3(k2_yellow_1(X1),X2,X3) != X2
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_48]),c_0_21]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_70,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_22])])).

cnf(c_0_71,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),X1,X2)) = k11_lattice3(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_67]),c_0_55]),c_0_48]),c_0_40]),c_0_21]),c_0_21]),c_0_21]),c_0_26]),c_0_22])])).

cnf(c_0_72,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_68]),c_0_48]),c_0_40]),c_0_21]),c_0_64]),c_0_22]),c_0_23])])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),X4)
    | k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X4)) != k11_lattice3(k2_yellow_1(X1),X2,X3)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_45]),c_0_55]),c_0_48]),c_0_21]),c_0_21]),c_0_21]),c_0_22])]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_64])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_57]),c_0_40]),c_0_26])]),c_0_52])).

cnf(c_0_76,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X2)) = k11_lattice3(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_63]),c_0_55]),c_0_48]),c_0_40]),c_0_21]),c_0_21]),c_0_26]),c_0_21]),c_0_22])])).

cnf(c_0_77,plain,
    ( k11_lattice3(k2_yellow_1(X1),X2,X3) = k11_lattice3(k2_yellow_1(X1),X3,X2)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_21]),c_0_48]),c_0_22])])).

cnf(c_0_78,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_32])])).

cnf(c_0_79,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),X2,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_40]),c_0_26])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_50]),c_0_26])]),c_0_52])).

cnf(c_0_81,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_32]),c_0_26]),c_0_80])])).

fof(c_0_82,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_83,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X5,X7)
      | r1_tarski(X5,k3_xboole_0(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_84,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_81]),c_0_40]),c_0_22])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | k11_lattice3(k2_yellow_1(X1),X3,X2) != X2
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_84]),c_0_32]),c_0_26]),c_0_80])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_87,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_40]),c_0_26]),c_0_64])]),c_0_52])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_79]),c_0_32]),c_0_64])]),c_0_92])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_75]),c_0_32])])).

cnf(c_0_96,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_94]),c_0_40]),c_0_32]),c_0_64])]),c_0_52]),c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_96]),c_0_40]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.21/0.45  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.029 s
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.21/0.45  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.21/0.45  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.21/0.45  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.21/0.45  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.21/0.45  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.21/0.45  fof(t25_yellow_0, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k12_lattice3(X1,X2,X3)<=>r3_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 0.21/0.45  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.21/0.45  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.21/0.45  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.21/0.45  fof(t16_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(v4_orders_2(X1)=>k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_lattice3)).
% 0.21/0.45  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 0.21/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.45  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.21/0.45  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.21/0.45  fof(c_0_15, plain, ![X10, X11, X12]:(v2_struct_0(X10)|~v3_orders_2(X10)|~l1_orders_2(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|r3_orders_2(X10,X11,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.21/0.45  fof(c_0_16, plain, ![X32]:(u1_struct_0(k2_yellow_1(X32))=X32&u1_orders_2(k2_yellow_1(X32))=k1_yellow_1(X32)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.21/0.45  fof(c_0_17, plain, ![X30]:(v1_orders_2(k2_yellow_1(X30))&l1_orders_2(k2_yellow_1(X30))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.21/0.45  fof(c_0_18, plain, ![X31]:(((v1_orders_2(k2_yellow_1(X31))&v3_orders_2(k2_yellow_1(X31)))&v4_orders_2(k2_yellow_1(X31)))&v5_orders_2(k2_yellow_1(X31))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.21/0.45  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk1_0)&(v2_lattice3(k2_yellow_1(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.21/0.45  cnf(c_0_20, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.45  cnf(c_0_21, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  cnf(c_0_22, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.45  cnf(c_0_23, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  cnf(c_0_25, plain, (r3_orders_2(k2_yellow_1(X1),X2,X2)|v2_struct_0(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.21/0.45  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_24, c_0_21])).
% 0.21/0.45  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  fof(c_0_28, plain, ![X17, X18, X19]:(~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|k12_lattice3(X17,X18,X19)=k11_lattice3(X17,X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.21/0.45  fof(c_0_29, plain, ![X27, X28, X29]:((X28!=k12_lattice3(X27,X28,X29)|r3_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(~v3_orders_2(X27)|~v5_orders_2(X27)|~v2_lattice3(X27)|~l1_orders_2(X27)))&(~r3_orders_2(X27,X28,X29)|X28=k12_lattice3(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(~v3_orders_2(X27)|~v5_orders_2(X27)|~v2_lattice3(X27)|~l1_orders_2(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).
% 0.21/0.45  fof(c_0_30, plain, ![X13]:(~l1_orders_2(X13)|(~v2_lattice3(X13)|~v2_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.21/0.45  cnf(c_0_31, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,X1)|v2_struct_0(k2_yellow_1(esk1_0))|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.45  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_27, c_0_21])).
% 0.21/0.45  fof(c_0_33, plain, ![X33, X34, X35]:((~r3_orders_2(k2_yellow_1(X33),X34,X35)|r1_tarski(X34,X35)|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))|~m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))|v1_xboole_0(X33))&(~r1_tarski(X34,X35)|r3_orders_2(k2_yellow_1(X33),X34,X35)|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))|~m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))|v1_xboole_0(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.21/0.45  fof(c_0_34, plain, ![X14, X15, X16]:(~l1_orders_2(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k11_lattice3(X14,X15,X16),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.21/0.45  fof(c_0_35, plain, ![X23, X24, X25, X26]:(~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|(~m1_subset_1(X25,u1_struct_0(X23))|(~m1_subset_1(X26,u1_struct_0(X23))|(~v4_orders_2(X23)|k11_lattice3(X23,k11_lattice3(X23,X24,X25),X26)=k11_lattice3(X23,X24,k11_lattice3(X23,X25,X26))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).
% 0.21/0.45  cnf(c_0_36, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.45  cnf(c_0_37, plain, (X2=k12_lattice3(X1,X2,X3)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.45  cnf(c_0_38, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.45  cnf(c_0_39, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.45  cnf(c_0_40, negated_conjecture, (v2_lattice3(k2_yellow_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  fof(c_0_41, plain, ![X20, X21, X22]:(~v5_orders_2(X20)|~v2_lattice3(X20)|~l1_orders_2(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|(~m1_subset_1(X22,u1_struct_0(X20))|k11_lattice3(X20,X21,X22)=k11_lattice3(X20,X22,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 0.21/0.45  cnf(c_0_42, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 0.21/0.45  cnf(c_0_43, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  cnf(c_0_44, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.45  cnf(c_0_45, plain, (k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  cnf(c_0_46, plain, (k11_lattice3(X1,X2,X3)=X2|~v5_orders_2(X1)|~v2_lattice3(X1)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.45  cnf(c_0_47, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_22])])).
% 0.21/0.45  cnf(c_0_48, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_49, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  cnf(c_0_50, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_42]), c_0_40]), c_0_22])])).
% 0.21/0.45  cnf(c_0_51, plain, (v1_xboole_0(X1)|r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_21]), c_0_21])).
% 0.21/0.45  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  cnf(c_0_53, plain, (m1_subset_1(k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)),u1_struct_0(X1))|~v4_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_44])).
% 0.21/0.45  cnf(c_0_54, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_40]), c_0_21]), c_0_32]), c_0_22]), c_0_23])])).
% 0.21/0.45  cnf(c_0_55, plain, (v4_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_56, plain, (k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))=k11_lattice3(X1,k11_lattice3(X1,X3,X4),X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_49, c_0_44])).
% 0.21/0.45  cnf(c_0_57, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_50]), c_0_48]), c_0_40]), c_0_21]), c_0_26]), c_0_22]), c_0_23])])).
% 0.21/0.45  cnf(c_0_58, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,esk3_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_52])).
% 0.21/0.45  cnf(c_0_59, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0),esk1_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_21]), c_0_55]), c_0_48]), c_0_40]), c_0_21]), c_0_32]), c_0_21]), c_0_22])])).
% 0.21/0.45  cnf(c_0_60, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0)=k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_48]), c_0_40]), c_0_21]), c_0_21]), c_0_26]), c_0_22])])).
% 0.21/0.45  cnf(c_0_61, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  cnf(c_0_62, plain, (r3_orders_2(X2,X1,X3)|X1!=k12_lattice3(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.45  cnf(c_0_63, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0)=X1|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_58]), c_0_48]), c_0_40]), c_0_21]), c_0_26]), c_0_21]), c_0_22]), c_0_23])])).
% 0.21/0.45  cnf(c_0_64, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_26]), c_0_32])])).
% 0.21/0.45  cnf(c_0_65, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_21]), c_0_21])).
% 0.21/0.45  cnf(c_0_66, plain, (r3_orders_2(X1,X2,X3)|k11_lattice3(X1,X2,X3)!=X2|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_62, c_0_36])).
% 0.21/0.45  cnf(c_0_67, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)=X1|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_63]), c_0_48]), c_0_40]), c_0_21]), c_0_26]), c_0_21]), c_0_22])])).
% 0.21/0.45  cnf(c_0_68, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))|v2_struct_0(k2_yellow_1(esk1_0))), inference(spm,[status(thm)],[c_0_31, c_0_64])).
% 0.21/0.45  cnf(c_0_69, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|k11_lattice3(k2_yellow_1(X1),X2,X3)!=X2|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_48]), c_0_21]), c_0_21]), c_0_22]), c_0_23])])).
% 0.21/0.45  cnf(c_0_70, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_22])])).
% 0.21/0.45  cnf(c_0_71, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),X1,X2))=k11_lattice3(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_67]), c_0_55]), c_0_48]), c_0_40]), c_0_21]), c_0_21]), c_0_21]), c_0_26]), c_0_22])])).
% 0.21/0.45  cnf(c_0_72, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_68]), c_0_48]), c_0_40]), c_0_21]), c_0_64]), c_0_22]), c_0_23])])).
% 0.21/0.45  cnf(c_0_73, plain, (v1_xboole_0(X1)|r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),X4)|k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X4))!=k11_lattice3(k2_yellow_1(X1),X2,X3)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_45]), c_0_55]), c_0_48]), c_0_21]), c_0_21]), c_0_21]), c_0_22])]), c_0_70])).
% 0.21/0.45  cnf(c_0_74, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))|~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_64])])).
% 0.21/0.45  cnf(c_0_75, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0),esk3_0)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_57]), c_0_40]), c_0_26])]), c_0_52])).
% 0.21/0.45  cnf(c_0_76, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X2))=k11_lattice3(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_63]), c_0_55]), c_0_48]), c_0_40]), c_0_21]), c_0_21]), c_0_26]), c_0_21]), c_0_22])])).
% 0.21/0.45  cnf(c_0_77, plain, (k11_lattice3(k2_yellow_1(X1),X2,X3)=k11_lattice3(k2_yellow_1(X1),X3,X2)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_21]), c_0_48]), c_0_22])])).
% 0.21/0.45  cnf(c_0_78, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_32])])).
% 0.21/0.45  cnf(c_0_79, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),X2,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_40]), c_0_26])])).
% 0.21/0.45  cnf(c_0_80, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_50]), c_0_26])]), c_0_52])).
% 0.21/0.45  cnf(c_0_81, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0)=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_32]), c_0_26]), c_0_80])])).
% 0.21/0.45  fof(c_0_82, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.45  fof(c_0_83, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X5,X7)|r1_tarski(X5,k3_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.21/0.45  cnf(c_0_84, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0)=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_81]), c_0_40]), c_0_22])])).
% 0.21/0.45  cnf(c_0_85, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  cnf(c_0_86, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.21/0.45  cnf(c_0_87, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.45  cnf(c_0_88, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|k11_lattice3(k2_yellow_1(X1),X3,X2)!=X2|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_77])).
% 0.21/0.45  cnf(c_0_89, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_84]), c_0_32]), c_0_26]), c_0_80])])).
% 0.21/0.45  cnf(c_0_90, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.21/0.45  cnf(c_0_91, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_87, c_0_86])).
% 0.21/0.45  cnf(c_0_92, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_40]), c_0_26]), c_0_64])]), c_0_52])).
% 0.21/0.45  cnf(c_0_93, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)|~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.45  cnf(c_0_94, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0)=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_79]), c_0_32]), c_0_64])]), c_0_92])])).
% 0.21/0.45  cnf(c_0_95, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_75]), c_0_32])])).
% 0.21/0.45  cnf(c_0_96, negated_conjecture, (v2_struct_0(k2_yellow_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_94]), c_0_40]), c_0_32]), c_0_64])]), c_0_52]), c_0_95])).
% 0.21/0.45  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_96]), c_0_40]), c_0_22])]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 98
% 0.21/0.45  # Proof object clause steps            : 69
% 0.21/0.45  # Proof object formula steps           : 29
% 0.21/0.45  # Proof object conjectures             : 42
% 0.21/0.45  # Proof object clause conjectures      : 39
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 22
% 0.21/0.45  # Proof object initial formulas used   : 14
% 0.21/0.45  # Proof object generating inferences   : 41
% 0.21/0.45  # Proof object simplifying inferences  : 157
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 14
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 25
% 0.21/0.45  # Removed in clause preprocessing      : 2
% 0.21/0.45  # Initial clauses in saturation        : 23
% 0.21/0.45  # Processed clauses                    : 282
% 0.21/0.45  # ...of these trivial                  : 11
% 0.21/0.45  # ...subsumed                          : 157
% 0.21/0.45  # ...remaining for further processing  : 114
% 0.21/0.45  # Other redundant clauses eliminated   : 0
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 6
% 0.21/0.45  # Backward-rewritten                   : 15
% 0.21/0.45  # Generated clauses                    : 2373
% 0.21/0.45  # ...of the previous two non-trivial   : 2208
% 0.21/0.45  # Contextual simplify-reflections      : 11
% 0.21/0.45  # Paramodulations                      : 2373
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 0
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 93
% 0.21/0.45  #    Positive orientable unit clauses  : 20
% 0.21/0.45  #    Positive unorientable unit clauses: 0
% 0.21/0.45  #    Negative unit clauses             : 7
% 0.21/0.45  #    Non-unit-clauses                  : 66
% 0.21/0.45  # Current number of unprocessed clauses: 1943
% 0.21/0.45  # ...number of literals in the above   : 12403
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 23
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 1236
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 389
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 128
% 0.21/0.45  # Unit Clause-clause subsumption calls : 105
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 23
% 0.21/0.45  # BW rewrite match successes           : 8
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 91908
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.094 s
% 0.21/0.45  # System time              : 0.010 s
% 0.21/0.45  # Total time               : 0.103 s
% 0.21/0.45  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
