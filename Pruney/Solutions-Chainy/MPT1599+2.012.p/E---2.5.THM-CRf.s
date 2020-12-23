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
% DateTime   : Thu Dec  3 11:15:44 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   98 (2036 expanded)
%              Number of clauses        :   71 ( 789 expanded)
%              Number of leaves         :   13 ( 564 expanded)
%              Depth                    :   19
%              Number of atoms          :  389 (6679 expanded)
%              Number of equality atoms :   53 (1504 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(t3_yellow_1,axiom,(
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

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

fof(c_0_14,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r3_orders_2(k2_yellow_1(X31),X32,X33)
        | r1_tarski(X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))
        | v1_xboole_0(X31) )
      & ( ~ r1_tarski(X32,X33)
        | r3_orders_2(k2_yellow_1(X31),X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_15,plain,(
    ! [X30] :
      ( u1_struct_0(k2_yellow_1(X30)) = X30
      & u1_orders_2(k2_yellow_1(X30)) = k1_yellow_1(X30) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v2_lattice3(k2_yellow_1(esk1_0))
    & m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ~ v5_orders_2(X15)
      | ~ v2_lattice3(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | k12_lattice3(X15,X16,X17) = k11_lattice3(X15,X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_18,plain,(
    ! [X25,X26,X27] :
      ( ( X26 != k12_lattice3(X25,X26,X27)
        | r3_orders_2(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v3_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v2_lattice3(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ r3_orders_2(X25,X26,X27)
        | X26 = k12_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v3_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v2_lattice3(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).

cnf(c_0_19,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | m1_subset_1(k11_lattice3(X12,X13,X14),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

cnf(c_0_23,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X2 = k12_lattice3(X1,X2,X3)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X29] :
      ( v1_orders_2(k2_yellow_1(X29))
      & v3_orders_2(k2_yellow_1(X29))
      & v4_orders_2(k2_yellow_1(X29))
      & v5_orders_2(k2_yellow_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_29,plain,(
    ! [X28] :
      ( v1_orders_2(k2_yellow_1(X28))
      & l1_orders_2(k2_yellow_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_34,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_39,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r3_orders_2(k2_yellow_1(u1_struct_0(X1)),X2,k11_lattice3(X1,X3,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,k11_lattice3(X1,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0) = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_20]),c_0_26]),c_0_20]),c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_38]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_26]),c_0_20]),c_0_37])]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0) = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_41]),c_0_34]),c_0_35]),c_0_36]),c_0_20]),c_0_38]),c_0_20]),c_0_37])])).

cnf(c_0_44,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,X2) = X1
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_42]),c_0_34]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_37])])).

fof(c_0_45,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_43]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_38]),c_0_20]),c_0_37])]),c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X3,esk1_0)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ r1_tarski(X3,esk3_0)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_37])]),c_0_27])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,X2) = X1
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_46]),c_0_34]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_37])])).

fof(c_0_50,plain,(
    ! [X18,X19,X20] :
      ( ~ v5_orders_2(X18)
      | ~ v2_lattice3(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | k11_lattice3(X18,X19,X20) = k11_lattice3(X18,X20,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

cnf(c_0_51,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk3_0,X1)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X3,esk1_0)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ r1_tarski(X3,esk2_0)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_49]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_37])]),c_0_27])).

fof(c_0_54,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ v5_orders_2(X21)
      | ~ v2_lattice3(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | ~ m1_subset_1(X24,u1_struct_0(X21))
      | ~ v4_orders_2(X21)
      | k11_lattice3(X21,k11_lattice3(X21,X22,X23),X24) = k11_lattice3(X21,X22,k11_lattice3(X21,X23,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).

cnf(c_0_55,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_52])])).

cnf(c_0_57,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk2_0,X1)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_38])).

cnf(c_0_58,plain,
    ( k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( v4_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_60,plain,
    ( k11_lattice3(k2_yellow_1(X1),X2,X3) = k11_lattice3(k2_yellow_1(X1),X3,X2)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_20]),c_0_36]),c_0_37])])).

cnf(c_0_61,plain,
    ( k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) = k11_lattice3(X1,k11_lattice3(X1,X3,X4),X2)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_62,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1) = esk3_0
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_56]),c_0_34]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_26]),c_0_37])])).

cnf(c_0_63,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk2_0,X1)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_38]),c_0_52])])).

cnf(c_0_64,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X2)) = k11_lattice3(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_43]),c_0_59]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_38]),c_0_20]),c_0_37])])).

cnf(c_0_65,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_66,plain,
    ( r3_orders_2(X2,X1,X3)
    | X1 != k12_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,X2) = k11_lattice3(k2_yellow_1(esk1_0),X2,X1)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_35])).

cnf(c_0_68,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0) = k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_tarski(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_20]),c_0_26]),c_0_37])])).

cnf(c_0_69,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1) = esk2_0
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_63]),c_0_34]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_38]),c_0_37])])).

cnf(c_0_70,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0) = k11_lattice3(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_49]),c_0_38])])).

fof(c_0_71,plain,(
    ! [X10,X11] : k1_setfam_1(k2_tarski(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_72,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X7,X9)
      | r1_tarski(X7,k3_xboole_0(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_20]),c_0_20])).

cnf(c_0_74,plain,
    ( r3_orders_2(X1,X2,X3)
    | k11_lattice3(X1,X2,X3) != X2
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_23])).

cnf(c_0_75,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_67]),c_0_26])])).

cnf(c_0_76,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_38])).

cnf(c_0_77,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_37])])).

cnf(c_0_78,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0) = esk2_0
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_38]),c_0_52])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_80,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | k11_lattice3(k2_yellow_1(X1),X2,X3) != X2
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_34]),c_0_36]),c_0_20]),c_0_20]),c_0_37])])).

cnf(c_0_83,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),X1,X2)) = k11_lattice3(k2_yellow_1(esk1_0),X1,X2)
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_75]),c_0_59]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_20]),c_0_26]),c_0_37])])).

cnf(c_0_84,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_26]),c_0_52])])).

cnf(c_0_85,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),X2,X3)) = k11_lattice3(k2_yellow_1(esk1_0),X2,k11_lattice3(k2_yellow_1(esk1_0),X3,X1))
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X3,esk1_0)
    | ~ m1_subset_1(X2,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_67]),c_0_59]),c_0_35]),c_0_36]),c_0_20]),c_0_20]),c_0_20]),c_0_37])]),c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_38]),c_0_52])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_81,c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k11_lattice3(k2_yellow_1(esk1_0),X2,X1) != X1
    | ~ m1_subset_1(X2,esk1_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_67]),c_0_35])]),c_0_27])).

cnf(c_0_90,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_38]),c_0_26]),c_0_52])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_84]),c_0_20]),c_0_20]),c_0_38]),c_0_20]),c_0_26]),c_0_37])])).

cnf(c_0_92,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0)) = k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_38])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_26]),c_0_91])])).

cnf(c_0_95,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_84]),c_0_26])])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_95]),c_0_38]),c_0_91])]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:46:38 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.52  #
% 0.18/0.52  # Preprocessing time       : 0.028 s
% 0.18/0.52  # Presaturation interreduction done
% 0.18/0.52  
% 0.18/0.52  # Proof found!
% 0.18/0.52  # SZS status Theorem
% 0.18/0.52  # SZS output start CNFRefutation
% 0.18/0.52  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.18/0.52  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.18/0.52  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.18/0.52  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.18/0.52  fof(t25_yellow_0, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k12_lattice3(X1,X2,X3)<=>r3_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_0)).
% 0.18/0.52  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.18/0.52  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.18/0.52  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.18/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.52  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 0.18/0.52  fof(t16_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(v4_orders_2(X1)=>k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_lattice3)).
% 0.18/0.52  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.18/0.52  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.18/0.52  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.18/0.52  fof(c_0_14, plain, ![X31, X32, X33]:((~r3_orders_2(k2_yellow_1(X31),X32,X33)|r1_tarski(X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))&(~r1_tarski(X32,X33)|r3_orders_2(k2_yellow_1(X31),X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.18/0.52  fof(c_0_15, plain, ![X30]:(u1_struct_0(k2_yellow_1(X30))=X30&u1_orders_2(k2_yellow_1(X30))=k1_yellow_1(X30)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.18/0.52  fof(c_0_16, negated_conjecture, (~v1_xboole_0(esk1_0)&(v2_lattice3(k2_yellow_1(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.18/0.52  fof(c_0_17, plain, ![X15, X16, X17]:(~v5_orders_2(X15)|~v2_lattice3(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|k12_lattice3(X15,X16,X17)=k11_lattice3(X15,X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.18/0.52  fof(c_0_18, plain, ![X25, X26, X27]:((X26!=k12_lattice3(X25,X26,X27)|r3_orders_2(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(~v3_orders_2(X25)|~v5_orders_2(X25)|~v2_lattice3(X25)|~l1_orders_2(X25)))&(~r3_orders_2(X25,X26,X27)|X26=k12_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(~v3_orders_2(X25)|~v5_orders_2(X25)|~v2_lattice3(X25)|~l1_orders_2(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).
% 0.18/0.52  cnf(c_0_19, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.52  cnf(c_0_20, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.52  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.52  fof(c_0_22, plain, ![X12, X13, X14]:(~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|m1_subset_1(k11_lattice3(X12,X13,X14),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.18/0.52  cnf(c_0_23, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.52  cnf(c_0_24, plain, (X2=k12_lattice3(X1,X2,X3)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  cnf(c_0_25, plain, (v1_xboole_0(X1)|r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 0.18/0.52  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.18/0.52  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.52  fof(c_0_28, plain, ![X29]:(((v1_orders_2(k2_yellow_1(X29))&v3_orders_2(k2_yellow_1(X29)))&v4_orders_2(k2_yellow_1(X29)))&v5_orders_2(k2_yellow_1(X29))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.18/0.52  fof(c_0_29, plain, ![X28]:(v1_orders_2(k2_yellow_1(X28))&l1_orders_2(k2_yellow_1(X28))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.18/0.52  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.52  cnf(c_0_31, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_32, plain, (k11_lattice3(X1,X2,X3)=X2|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.52  cnf(c_0_33, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,esk3_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.18/0.52  cnf(c_0_34, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.52  cnf(c_0_35, negated_conjecture, (v2_lattice3(k2_yellow_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.52  cnf(c_0_36, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.52  cnf(c_0_37, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.52  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_30, c_0_20])).
% 0.18/0.52  cnf(c_0_39, plain, (v1_xboole_0(u1_struct_0(X1))|r3_orders_2(k2_yellow_1(u1_struct_0(X1)),X2,k11_lattice3(X1,X3,X4))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~r1_tarski(X2,k11_lattice3(X1,X3,X4))), inference(spm,[status(thm)],[c_0_25, c_0_31])).
% 0.18/0.52  cnf(c_0_40, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0)=X1|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_20]), c_0_26]), c_0_20]), c_0_37])])).
% 0.18/0.52  cnf(c_0_41, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,esk2_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_38]), c_0_27])).
% 0.18/0.52  cnf(c_0_42, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk1_0)|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_26]), c_0_20]), c_0_37])]), c_0_27])).
% 0.18/0.52  cnf(c_0_43, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0)=X1|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_41]), c_0_34]), c_0_35]), c_0_36]), c_0_20]), c_0_38]), c_0_20]), c_0_37])])).
% 0.18/0.52  cnf(c_0_44, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,X2)=X1|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_42]), c_0_34]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_37])])).
% 0.18/0.52  fof(c_0_45, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.52  cnf(c_0_46, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk1_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_43]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_38]), c_0_20]), c_0_37])]), c_0_27])).
% 0.18/0.52  cnf(c_0_47, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X3,esk1_0)|~m1_subset_1(X2,esk1_0)|~r1_tarski(X3,esk3_0)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_44]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_37])]), c_0_27])).
% 0.18/0.52  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.52  cnf(c_0_49, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,X2)=X1|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_46]), c_0_34]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_37])])).
% 0.18/0.52  fof(c_0_50, plain, ![X18, X19, X20]:(~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~m1_subset_1(X20,u1_struct_0(X18))|k11_lattice3(X18,X19,X20)=k11_lattice3(X18,X20,X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 0.18/0.52  cnf(c_0_51, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk3_0,X1)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X2,esk3_0)|~r1_tarski(esk3_0,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_26])).
% 0.18/0.52  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.18/0.52  cnf(c_0_53, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X3,esk1_0)|~m1_subset_1(X2,esk1_0)|~r1_tarski(X3,esk2_0)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_49]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_37])]), c_0_27])).
% 0.18/0.52  fof(c_0_54, plain, ![X21, X22, X23, X24]:(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)|(~m1_subset_1(X22,u1_struct_0(X21))|(~m1_subset_1(X23,u1_struct_0(X21))|(~m1_subset_1(X24,u1_struct_0(X21))|(~v4_orders_2(X21)|k11_lattice3(X21,k11_lattice3(X21,X22,X23),X24)=k11_lattice3(X21,X22,k11_lattice3(X21,X23,X24))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).
% 0.18/0.52  cnf(c_0_55, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.52  cnf(c_0_56, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk3_0,X1)|~m1_subset_1(X1,esk1_0)|~r1_tarski(esk3_0,X1)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_52])])).
% 0.18/0.52  cnf(c_0_57, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk2_0,X1)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_38])).
% 0.18/0.52  cnf(c_0_58, plain, (k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.52  cnf(c_0_59, plain, (v4_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.52  cnf(c_0_60, plain, (k11_lattice3(k2_yellow_1(X1),X2,X3)=k11_lattice3(k2_yellow_1(X1),X3,X2)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_20]), c_0_36]), c_0_37])])).
% 0.18/0.52  cnf(c_0_61, plain, (k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))=k11_lattice3(X1,k11_lattice3(X1,X3,X4),X2)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_31])).
% 0.18/0.52  cnf(c_0_62, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)=esk3_0|~m1_subset_1(X1,esk1_0)|~r1_tarski(esk3_0,X1)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_56]), c_0_34]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_26]), c_0_37])])).
% 0.18/0.52  cnf(c_0_63, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk2_0,X1)|~m1_subset_1(X1,esk1_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_38]), c_0_52])])).
% 0.18/0.52  cnf(c_0_64, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X2))=k11_lattice3(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_43]), c_0_59]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_38]), c_0_20]), c_0_37])])).
% 0.18/0.52  cnf(c_0_65, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.52  cnf(c_0_66, plain, (r3_orders_2(X2,X1,X3)|X1!=k12_lattice3(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  cnf(c_0_67, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,X2)=k11_lattice3(k2_yellow_1(esk1_0),X2,X1)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_60, c_0_35])).
% 0.18/0.52  cnf(c_0_68, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,esk3_0)=k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk1_0)|~r1_tarski(esk3_0,X2)|~r1_tarski(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_20]), c_0_26]), c_0_37])])).
% 0.18/0.52  cnf(c_0_69, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1)=esk2_0|~m1_subset_1(X1,esk1_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_63]), c_0_34]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_38]), c_0_37])])).
% 0.18/0.52  cnf(c_0_70, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0)=k11_lattice3(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(esk2_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_49]), c_0_38])])).
% 0.18/0.52  fof(c_0_71, plain, ![X10, X11]:k1_setfam_1(k2_tarski(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.18/0.52  fof(c_0_72, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X7,X9)|r1_tarski(X7,k3_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.18/0.52  cnf(c_0_73, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_20]), c_0_20])).
% 0.18/0.52  cnf(c_0_74, plain, (r3_orders_2(X1,X2,X3)|k11_lattice3(X1,X2,X3)!=X2|~v3_orders_2(X1)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_66, c_0_23])).
% 0.18/0.52  cnf(c_0_75, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)=X1|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_67]), c_0_26])])).
% 0.18/0.52  cnf(c_0_76, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0)=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(esk3_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_38])).
% 0.18/0.52  cnf(c_0_77, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_37])])).
% 0.18/0.52  cnf(c_0_78, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0)=esk2_0|~m1_subset_1(X1,esk1_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_38]), c_0_52])])).
% 0.18/0.52  cnf(c_0_79, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.52  cnf(c_0_80, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.18/0.52  cnf(c_0_81, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.18/0.52  cnf(c_0_82, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|k11_lattice3(k2_yellow_1(X1),X2,X3)!=X2|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_34]), c_0_36]), c_0_20]), c_0_20]), c_0_37])])).
% 0.18/0.52  cnf(c_0_83, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),X1,X2))=k11_lattice3(k2_yellow_1(esk1_0),X1,X2)|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_75]), c_0_59]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_20]), c_0_26]), c_0_37])])).
% 0.18/0.52  cnf(c_0_84, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk2_0)=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_26]), c_0_52])])).
% 0.18/0.52  cnf(c_0_85, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,k11_lattice3(k2_yellow_1(esk1_0),X2,X3))=k11_lattice3(k2_yellow_1(esk1_0),X2,k11_lattice3(k2_yellow_1(esk1_0),X3,X1))|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X3,esk1_0)|~m1_subset_1(X2,esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_67]), c_0_59]), c_0_35]), c_0_36]), c_0_20]), c_0_20]), c_0_20]), c_0_37])]), c_0_77])).
% 0.18/0.52  cnf(c_0_86, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_38]), c_0_52])])).
% 0.18/0.52  cnf(c_0_87, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.18/0.52  cnf(c_0_88, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_81, c_0_80])).
% 0.18/0.52  cnf(c_0_89, negated_conjecture, (r1_tarski(X1,X2)|k11_lattice3(k2_yellow_1(esk1_0),X2,X1)!=X1|~m1_subset_1(X2,esk1_0)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_67]), c_0_35])]), c_0_27])).
% 0.18/0.52  cnf(c_0_90, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_38]), c_0_26]), c_0_52])])).
% 0.18/0.52  cnf(c_0_91, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_84]), c_0_20]), c_0_20]), c_0_38]), c_0_20]), c_0_26]), c_0_37])])).
% 0.18/0.52  cnf(c_0_92, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0))=k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_38])])).
% 0.18/0.52  cnf(c_0_93, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)|~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.18/0.52  cnf(c_0_94, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_26]), c_0_91])])).
% 0.18/0.52  cnf(c_0_95, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_84]), c_0_26])])).
% 0.18/0.52  cnf(c_0_96, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])])).
% 0.18/0.52  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_95]), c_0_38]), c_0_91])]), c_0_96]), ['proof']).
% 0.18/0.52  # SZS output end CNFRefutation
% 0.18/0.52  # Proof object total steps             : 98
% 0.18/0.52  # Proof object clause steps            : 71
% 0.18/0.52  # Proof object formula steps           : 27
% 0.18/0.52  # Proof object conjectures             : 47
% 0.18/0.52  # Proof object clause conjectures      : 44
% 0.18/0.52  # Proof object formula conjectures     : 3
% 0.18/0.52  # Proof object initial clauses used    : 21
% 0.18/0.52  # Proof object initial formulas used   : 13
% 0.18/0.52  # Proof object generating inferences   : 42
% 0.18/0.52  # Proof object simplifying inferences  : 179
% 0.18/0.52  # Training examples: 0 positive, 0 negative
% 0.18/0.52  # Parsed axioms                        : 13
% 0.18/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.52  # Initial clauses                      : 26
% 0.18/0.52  # Removed in clause preprocessing      : 2
% 0.18/0.52  # Initial clauses in saturation        : 24
% 0.18/0.52  # Processed clauses                    : 1552
% 0.18/0.52  # ...of these trivial                  : 11
% 0.18/0.52  # ...subsumed                          : 1324
% 0.18/0.52  # ...remaining for further processing  : 217
% 0.18/0.52  # Other redundant clauses eliminated   : 50
% 0.18/0.52  # Clauses deleted for lack of memory   : 0
% 0.18/0.52  # Backward-subsumed                    : 12
% 0.18/0.52  # Backward-rewritten                   : 16
% 0.18/0.52  # Generated clauses                    : 8378
% 0.18/0.52  # ...of the previous two non-trivial   : 7514
% 0.18/0.52  # Contextual simplify-reflections      : 30
% 0.18/0.52  # Paramodulations                      : 8328
% 0.18/0.52  # Factorizations                       : 0
% 0.18/0.52  # Equation resolutions                 : 50
% 0.18/0.52  # Propositional unsat checks           : 0
% 0.18/0.52  #    Propositional check models        : 0
% 0.18/0.52  #    Propositional check unsatisfiable : 0
% 0.18/0.52  #    Propositional clauses             : 0
% 0.18/0.52  #    Propositional clauses after purity: 0
% 0.18/0.52  #    Propositional unsat core size     : 0
% 0.18/0.52  #    Propositional preprocessing time  : 0.000
% 0.18/0.52  #    Propositional encoding time       : 0.000
% 0.18/0.52  #    Propositional solver time         : 0.000
% 0.18/0.52  #    Success case prop preproc time    : 0.000
% 0.18/0.52  #    Success case prop encoding time   : 0.000
% 0.18/0.52  #    Success case prop solver time     : 0.000
% 0.18/0.52  # Current number of processed clauses  : 165
% 0.18/0.52  #    Positive orientable unit clauses  : 17
% 0.18/0.52  #    Positive unorientable unit clauses: 0
% 0.18/0.52  #    Negative unit clauses             : 9
% 0.18/0.52  #    Non-unit-clauses                  : 139
% 0.18/0.52  # Current number of unprocessed clauses: 5918
% 0.18/0.52  # ...number of literals in the above   : 40875
% 0.18/0.52  # Current number of archived formulas  : 0
% 0.18/0.52  # Current number of archived clauses   : 52
% 0.18/0.52  # Clause-clause subsumption calls (NU) : 7227
% 0.18/0.52  # Rec. Clause-clause subsumption calls : 2469
% 0.18/0.52  # Non-unit clause-clause subsumptions  : 549
% 0.18/0.52  # Unit Clause-clause subsumption calls : 193
% 0.18/0.52  # Rewrite failures with RHS unbound    : 0
% 0.18/0.52  # BW rewrite match attempts            : 48
% 0.18/0.52  # BW rewrite match successes           : 7
% 0.18/0.52  # Condensation attempts                : 0
% 0.18/0.52  # Condensation successes               : 0
% 0.18/0.52  # Termbank termtop insertions          : 311485
% 0.18/0.52  
% 0.18/0.52  # -------------------------------------------------
% 0.18/0.52  # User time                : 0.187 s
% 0.18/0.52  # System time              : 0.006 s
% 0.18/0.52  # Total time               : 0.194 s
% 0.18/0.52  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
