%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   86 (1142 expanded)
%              Number of clauses        :   59 ( 480 expanded)
%              Number of leaves         :   13 ( 298 expanded)
%              Depth                    :   13
%              Number of atoms          :  289 (2909 expanded)
%              Number of equality atoms :   34 ( 509 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

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

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

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

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

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

fof(c_0_14,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v2_lattice3(k2_yellow_1(esk1_0))
    & m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X28] : k2_yellow_1(X28) = g1_orders_2(X28,k1_yellow_1(X28)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_16,plain,(
    ! [X29] :
      ( v1_orders_2(k2_yellow_1(X29))
      & l1_orders_2(k2_yellow_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_17,plain,(
    ! [X30] :
      ( v1_orders_2(k2_yellow_1(X30))
      & v3_orders_2(k2_yellow_1(X30))
      & v4_orders_2(k2_yellow_1(X30))
      & v5_orders_2(k2_yellow_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v3_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | r3_orders_2(X8,X9,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_26,plain,
    ( v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_28,plain,(
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

fof(c_0_29,plain,(
    ! [X15,X16,X17] :
      ( ~ v5_orders_2(X15)
      | ~ v2_lattice3(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | k12_lattice3(X15,X16,X17) = k11_lattice3(X15,X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_30,plain,(
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

fof(c_0_31,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ v2_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_32,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X1)
    | v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_20])).

fof(c_0_35,plain,(
    ! [X18,X19,X20] :
      ( ~ v5_orders_2(X18)
      | ~ v2_lattice3(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | k11_lattice3(X18,X19,X20) = k11_lattice3(X18,X20,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

cnf(c_0_36,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( X2 = k12_lattice3(X1,X2,X3)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)
    | v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( v2_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)
    | v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

fof(c_0_44,plain,(
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

cnf(c_0_45,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_47,plain,
    ( v4_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,plain,
    ( r3_orders_2(X2,X1,X3)
    | X1 != k12_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_25])])).

fof(c_0_53,plain,(
    ! [X12,X13,X14] :
      ( ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | m1_subset_1(k11_lattice3(X12,X13,X14),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

cnf(c_0_54,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_43]),c_0_42]),c_0_25])])).

cnf(c_0_55,plain,
    ( k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_46]),c_0_42]),c_0_25])])).

cnf(c_0_57,plain,
    ( v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_49])).

cnf(c_0_59,plain,
    ( r3_orders_2(X1,X2,X3)
    | k11_lattice3(X1,X2,X3) != X2
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_46]),c_0_42]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_54]),c_0_46]),c_0_42]),c_0_34]),c_0_25]),c_0_26])])).

cnf(c_0_63,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X2)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X2,esk3_0))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X2),u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_46]),c_0_42]),c_0_24]),c_0_25])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_65,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X5,X7)
      | r1_tarski(X5,k3_xboole_0(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0) != X1
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_46]),c_0_42]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_67,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_60]),c_0_57]),c_0_46]),c_0_42]),c_0_24]),c_0_25])])).

cnf(c_0_68,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_46]),c_0_42]),c_0_25])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1),u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_24]),c_0_25])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_62]),c_0_57]),c_0_46]),c_0_42]),c_0_34]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_62]),c_0_34])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_20])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_56])).

cnf(c_0_76,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_34]),c_0_24])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_34]),c_0_24])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0) != X1
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_59]),c_0_46]),c_0_42]),c_0_34]),c_0_25]),c_0_26])])).

cnf(c_0_79,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk2_0) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_24])])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_77])]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:35:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.031 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.13/0.39  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.13/0.39  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.13/0.39  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.13/0.39  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.13/0.39  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.13/0.39  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.13/0.39  fof(t25_yellow_0, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k12_lattice3(X1,X2,X3)<=>r3_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 0.13/0.39  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.13/0.39  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 0.13/0.39  fof(t16_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(v4_orders_2(X1)=>k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_lattice3)).
% 0.13/0.39  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.13/0.39  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.13/0.39  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.13/0.39  fof(c_0_14, negated_conjecture, (~v1_xboole_0(esk1_0)&(v2_lattice3(k2_yellow_1(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.39  fof(c_0_15, plain, ![X28]:k2_yellow_1(X28)=g1_orders_2(X28,k1_yellow_1(X28)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.13/0.39  fof(c_0_16, plain, ![X29]:(v1_orders_2(k2_yellow_1(X29))&l1_orders_2(k2_yellow_1(X29))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.13/0.39  fof(c_0_17, plain, ![X30]:(((v1_orders_2(k2_yellow_1(X30))&v3_orders_2(k2_yellow_1(X30)))&v4_orders_2(k2_yellow_1(X30)))&v5_orders_2(k2_yellow_1(X30))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.13/0.39  fof(c_0_18, plain, ![X8, X9, X10]:(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))|r3_orders_2(X8,X9,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_20, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_21, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_22, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_23, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  cnf(c_0_25, plain, (l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.13/0.39  cnf(c_0_26, plain, (v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_28, plain, ![X31, X32, X33]:((~r3_orders_2(k2_yellow_1(X31),X32,X33)|r1_tarski(X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))&(~r1_tarski(X32,X33)|r3_orders_2(k2_yellow_1(X31),X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.13/0.39  fof(c_0_29, plain, ![X15, X16, X17]:(~v5_orders_2(X15)|~v2_lattice3(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|k12_lattice3(X15,X16,X17)=k11_lattice3(X15,X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.13/0.39  fof(c_0_30, plain, ![X25, X26, X27]:((X26!=k12_lattice3(X25,X26,X27)|r3_orders_2(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(~v3_orders_2(X25)|~v5_orders_2(X25)|~v2_lattice3(X25)|~l1_orders_2(X25)))&(~r3_orders_2(X25,X26,X27)|X26=k12_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(~v3_orders_2(X25)|~v5_orders_2(X25)|~v2_lattice3(X25)|~l1_orders_2(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).
% 0.13/0.39  fof(c_0_31, plain, ![X11]:(~l1_orders_2(X11)|(~v2_lattice3(X11)|~v2_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X1)|v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (v2_lattice3(k2_yellow_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(rw,[status(thm)],[c_0_27, c_0_20])).
% 0.13/0.39  fof(c_0_35, plain, ![X18, X19, X20]:(~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~m1_subset_1(X20,u1_struct_0(X18))|k11_lattice3(X18,X19,X20)=k11_lattice3(X18,X20,X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 0.13/0.39  cnf(c_0_36, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_37, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_38, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_39, plain, (X2=k12_lattice3(X1,X2,X3)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_40, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)|v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_24])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (v2_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))), inference(rw,[status(thm)],[c_0_33, c_0_20])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)|v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 0.13/0.39  fof(c_0_44, plain, ![X21, X22, X23, X24]:(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)|(~m1_subset_1(X22,u1_struct_0(X21))|(~m1_subset_1(X23,u1_struct_0(X21))|(~m1_subset_1(X24,u1_struct_0(X21))|(~v4_orders_2(X21)|k11_lattice3(X21,k11_lattice3(X21,X22,X23),X24)=k11_lattice3(X21,X22,k11_lattice3(X21,X23,X24))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).
% 0.13/0.39  cnf(c_0_45, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_46, plain, (v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_36, c_0_20])).
% 0.13/0.39  cnf(c_0_47, plain, (v4_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_48, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_20]), c_0_20]), c_0_20])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_50, plain, (r3_orders_2(X2,X1,X3)|X1!=k12_lattice3(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_51, plain, (k11_lattice3(X1,X2,X3)=X2|~v5_orders_2(X1)|~v2_lattice3(X1)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_25])])).
% 0.13/0.39  fof(c_0_53, plain, ![X12, X13, X14]:(~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|m1_subset_1(k11_lattice3(X12,X13,X14),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_43]), c_0_42]), c_0_25])])).
% 0.13/0.39  cnf(c_0_55, plain, (k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0)=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_46]), c_0_42]), c_0_25])])).
% 0.13/0.39  cnf(c_0_57, plain, (v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_47, c_0_20])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (r1_tarski(X1,esk3_0)|~r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_24]), c_0_49])).
% 0.13/0.39  cnf(c_0_59, plain, (r3_orders_2(X1,X2,X3)|k11_lattice3(X1,X2,X3)!=X2|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_50, c_0_38])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_46]), c_0_42]), c_0_24]), c_0_25]), c_0_26])])).
% 0.13/0.39  cnf(c_0_61, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_54]), c_0_46]), c_0_42]), c_0_34]), c_0_25]), c_0_26])])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X2))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X2,esk3_0))|~m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X2),u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_46]), c_0_42]), c_0_24]), c_0_25])])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_65, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X5,X7)|r1_tarski(X5,k3_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,esk3_0)|k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0)!=X1|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_46]), c_0_42]), c_0_24]), c_0_25]), c_0_26])])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_60]), c_0_57]), c_0_46]), c_0_42]), c_0_24]), c_0_25])])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_34]), c_0_46]), c_0_42]), c_0_25])])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1),u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_24]), c_0_25])])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (r1_tarski(X1,esk2_0)|~r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_49])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_62]), c_0_57]), c_0_46]), c_0_42]), c_0_34]), c_0_25])])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_62]), c_0_34])])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_64, c_0_20])).
% 0.13/0.39  cnf(c_0_74, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,esk3_0)|k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)!=X1|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(spm,[status(thm)],[c_0_66, c_0_56])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_34]), c_0_24])])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_34]), c_0_24])])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (r1_tarski(X1,esk2_0)|k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)!=X1|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_59]), c_0_46]), c_0_42]), c_0_34]), c_0_25]), c_0_26])])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk2_0)=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_24])])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0)|~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (r1_tarski(X1,esk2_0)|k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)!=X1|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(spm,[status(thm)],[c_0_78, c_0_68])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_72, c_0_79])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_77])]), c_0_84]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 86
% 0.13/0.39  # Proof object clause steps            : 59
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 40
% 0.13/0.39  # Proof object clause conjectures      : 37
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 20
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 28
% 0.13/0.39  # Proof object simplifying inferences  : 93
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 23
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 22
% 0.13/0.39  # Processed clauses                    : 112
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 34
% 0.13/0.39  # ...remaining for further processing  : 77
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 5
% 0.13/0.39  # Generated clauses                    : 716
% 0.13/0.39  # ...of the previous two non-trivial   : 616
% 0.13/0.39  # Contextual simplify-reflections      : 3
% 0.13/0.39  # Paramodulations                      : 716
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
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
% 0.13/0.39  # Current number of processed clauses  : 72
% 0.13/0.39  #    Positive orientable unit clauses  : 19
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 7
% 0.13/0.39  #    Non-unit-clauses                  : 46
% 0.13/0.39  # Current number of unprocessed clauses: 512
% 0.13/0.39  # ...number of literals in the above   : 2589
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 6
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 358
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 205
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 16
% 0.13/0.39  # Unit Clause-clause subsumption calls : 55
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 25
% 0.13/0.39  # BW rewrite match successes           : 5
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 37655
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.051 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.058 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
