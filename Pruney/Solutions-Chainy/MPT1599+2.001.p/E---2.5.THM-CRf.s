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
% DateTime   : Thu Dec  3 11:15:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 403 expanded)
%              Number of clauses        :   51 ( 172 expanded)
%              Number of leaves         :   10 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  314 (1168 expanded)
%              Number of equality atoms :   17 ( 157 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   74 (   3 average)
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

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

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

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

fof(c_0_11,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v2_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X28] : k2_yellow_1(X28) = g1_orders_2(X28,k1_yellow_1(X28)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_13,plain,(
    ! [X29] :
      ( v1_orders_2(k2_yellow_1(X29))
      & l1_orders_2(k2_yellow_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( r1_orders_2(X22,X25,X23)
        | X25 != k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X25,X24)
        | X25 != k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X22))
        | ~ r1_orders_2(X22,X26,X23)
        | ~ r1_orders_2(X22,X26,X24)
        | r1_orders_2(X22,X26,X25)
        | X25 != k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk1_4(X22,X23,X24,X25),u1_struct_0(X22))
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X23)
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X24)
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X25)
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_15,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | ~ v2_lattice3(X18)
      | ~ v2_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_16,plain,(
    ! [X30] :
      ( v1_orders_2(k2_yellow_1(X30))
      & v3_orders_2(k2_yellow_1(X30))
      & v4_orders_2(k2_yellow_1(X30))
      & v5_orders_2(k2_yellow_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_17,plain,(
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

cnf(c_0_18,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_27,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r3_orders_2(X15,X16,X17)
        | r1_orders_2(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) )
      & ( ~ r1_orders_2(X15,X16,X17)
        | r3_orders_2(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_28,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v2_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_30,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_33,plain,
    ( v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_36,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_40,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | m1_subset_1(k11_lattice3(X19,X20,X21),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

cnf(c_0_41,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_29]),c_0_30])])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2)
    | X1 != k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_29]),c_0_30])])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_19])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_49,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0)
    | ~ r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_42]),c_0_30])]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X1),X1)
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X1),u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2)
    | X1 != k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X2,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_33]),c_0_29]),c_0_30])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)
    | ~ r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)
    | ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_30])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)
    | ~ r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_30])])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_49]),c_0_32]),c_0_30])])).

cnf(c_0_58,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk3_0)
    | ~ r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_42]),c_0_30])]),c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),X1)
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)
    | ~ r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_38]),c_0_32])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)
    | ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_49]),c_0_30])])).

cnf(c_0_62,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk4_0)
    | ~ r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_38])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)
    | ~ r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_30])])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_49]),c_0_38]),c_0_30])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)
    | ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_38]),c_0_32])])).

cnf(c_0_67,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_32]),c_0_63])])).

cnf(c_0_68,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk3_0)
    | ~ r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( ~ r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_32]),c_0_69])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.21/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.029 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.21/0.40  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.21/0.40  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.21/0.40  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 0.21/0.40  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.21/0.40  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.21/0.40  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.21/0.40  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.21/0.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.21/0.40  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.21/0.40  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.21/0.40  fof(c_0_11, negated_conjecture, (~v1_xboole_0(esk2_0)&(v2_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.21/0.40  fof(c_0_12, plain, ![X28]:k2_yellow_1(X28)=g1_orders_2(X28,k1_yellow_1(X28)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.21/0.40  fof(c_0_13, plain, ![X29]:(v1_orders_2(k2_yellow_1(X29))&l1_orders_2(k2_yellow_1(X29))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.21/0.40  fof(c_0_14, plain, ![X22, X23, X24, X25, X26]:((((r1_orders_2(X22,X25,X23)|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,X25,X24)|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&(~m1_subset_1(X26,u1_struct_0(X22))|(~r1_orders_2(X22,X26,X23)|~r1_orders_2(X22,X26,X24)|r1_orders_2(X22,X26,X25))|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&((m1_subset_1(esk1_4(X22,X23,X24,X25),u1_struct_0(X22))|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(((r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X23)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X24)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&(~r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X25)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.21/0.40  fof(c_0_15, plain, ![X18]:(~l1_orders_2(X18)|(~v2_lattice3(X18)|~v2_struct_0(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.21/0.40  fof(c_0_16, plain, ![X30]:(((v1_orders_2(k2_yellow_1(X30))&v3_orders_2(k2_yellow_1(X30)))&v4_orders_2(k2_yellow_1(X30)))&v5_orders_2(k2_yellow_1(X30))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.21/0.40  fof(c_0_17, plain, ![X31, X32, X33]:((~r3_orders_2(k2_yellow_1(X31),X32,X33)|r1_tarski(X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))&(~r1_tarski(X32,X33)|r3_orders_2(k2_yellow_1(X31),X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (v2_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_19, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_20, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_21, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_22, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_24, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_25, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  fof(c_0_27, plain, ![X15, X16, X17]:((~r3_orders_2(X15,X16,X17)|r1_orders_2(X15,X16,X17)|(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))&(~r1_orders_2(X15,X16,X17)|r3_orders_2(X15,X16,X17)|(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.21/0.40  cnf(c_0_28, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_29, negated_conjecture, (v2_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.40  cnf(c_0_30, plain, (l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.21/0.40  cnf(c_0_31, plain, (r1_orders_2(X1,X2,X3)|X2!=k11_lattice3(X1,X4,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(rw,[status(thm)],[c_0_23, c_0_19])).
% 0.21/0.40  cnf(c_0_33, plain, (v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_24, c_0_19])).
% 0.21/0.40  cnf(c_0_34, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X3,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  fof(c_0_36, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.21/0.40  cnf(c_0_37, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_19]), c_0_19]), c_0_19])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 0.21/0.40  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  fof(c_0_40, plain, ![X19, X20, X21]:(~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|m1_subset_1(k11_lattice3(X19,X20,X21),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.21/0.40  cnf(c_0_41, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.40  cnf(c_0_42, plain, (v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_28, c_0_19])).
% 0.21/0.40  cnf(c_0_43, negated_conjecture, (~v2_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_29]), c_0_30])])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2)|X1!=k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X2)|~m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_29]), c_0_30])])).
% 0.21/0.40  cnf(c_0_45, plain, (r1_orders_2(X1,X2,X3)|X2!=k11_lattice3(X1,X3,X4)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_34, c_0_22])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_35, c_0_19])).
% 0.21/0.40  cnf(c_0_47, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.40  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,esk4_0)|~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.21/0.40  cnf(c_0_49, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.40  cnf(c_0_50, negated_conjecture, (r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0)|~r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_42]), c_0_30])]), c_0_43])).
% 0.21/0.40  cnf(c_0_51, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X1),X1)|~m1_subset_1(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X1),u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(er,[status(thm)],[c_0_44])).
% 0.21/0.40  cnf(c_0_52, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2)|X1!=k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X2,esk4_0)|~m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_33]), c_0_29]), c_0_30])])).
% 0.21/0.40  cnf(c_0_53, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)|~r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)|~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)|~m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_30])])).
% 0.21/0.40  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,esk3_0)|~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_39])).
% 0.21/0.40  cnf(c_0_56, negated_conjecture, (r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)|~r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk4_0)|~m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_30])])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,X1),X1)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_49]), c_0_32]), c_0_30])])).
% 0.21/0.40  cnf(c_0_58, negated_conjecture, (r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk3_0)|~r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_42]), c_0_30])]), c_0_43])).
% 0.21/0.40  cnf(c_0_59, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),X1)|~m1_subset_1(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(er,[status(thm)],[c_0_52])).
% 0.21/0.40  cnf(c_0_60, negated_conjecture, (~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)|~r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_38]), c_0_32])])).
% 0.21/0.40  cnf(c_0_61, negated_conjecture, (r1_tarski(k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)|~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)|~m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_49]), c_0_30])])).
% 0.21/0.40  cnf(c_0_62, negated_conjecture, (r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk4_0)|~r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk4_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(spm,[status(thm)],[c_0_56, c_0_38])).
% 0.21/0.40  cnf(c_0_63, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 0.21/0.40  cnf(c_0_64, negated_conjecture, (r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)|~r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,X2),esk3_0)|~m1_subset_1(X2,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_30])])).
% 0.21/0.40  cnf(c_0_65, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_49]), c_0_38]), c_0_30])])).
% 0.21/0.40  cnf(c_0_66, negated_conjecture, (~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)|~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_38]), c_0_32])])).
% 0.21/0.40  cnf(c_0_67, negated_conjecture, (r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_32]), c_0_63])])).
% 0.21/0.40  cnf(c_0_68, negated_conjecture, (r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk3_0)|~r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),X1,esk4_0),esk3_0)|~m1_subset_1(X1,u1_struct_0(g1_orders_2(esk2_0,k1_yellow_1(esk2_0))))), inference(spm,[status(thm)],[c_0_64, c_0_38])).
% 0.21/0.40  cnf(c_0_69, negated_conjecture, (r1_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_32])).
% 0.21/0.40  cnf(c_0_70, negated_conjecture, (~r3_orders_2(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),k11_lattice3(g1_orders_2(esk2_0,k1_yellow_1(esk2_0)),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.21/0.40  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_32]), c_0_69])]), c_0_70]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 72
% 0.21/0.40  # Proof object clause steps            : 51
% 0.21/0.40  # Proof object formula steps           : 21
% 0.21/0.40  # Proof object conjectures             : 37
% 0.21/0.40  # Proof object clause conjectures      : 34
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 16
% 0.21/0.40  # Proof object initial formulas used   : 10
% 0.21/0.40  # Proof object generating inferences   : 24
% 0.21/0.40  # Proof object simplifying inferences  : 59
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 13
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 30
% 0.21/0.40  # Removed in clause preprocessing      : 1
% 0.21/0.40  # Initial clauses in saturation        : 29
% 0.21/0.40  # Processed clauses                    : 244
% 0.21/0.40  # ...of these trivial                  : 1
% 0.21/0.40  # ...subsumed                          : 62
% 0.21/0.40  # ...remaining for further processing  : 181
% 0.21/0.40  # Other redundant clauses eliminated   : 2
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 6
% 0.21/0.40  # Backward-rewritten                   : 2
% 0.21/0.40  # Generated clauses                    : 344
% 0.21/0.40  # ...of the previous two non-trivial   : 298
% 0.21/0.40  # Contextual simplify-reflections      : 9
% 0.21/0.40  # Paramodulations                      : 327
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 17
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 145
% 0.21/0.40  #    Positive orientable unit clauses  : 19
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 5
% 0.21/0.40  #    Non-unit-clauses                  : 121
% 0.21/0.40  # Current number of unprocessed clauses: 105
% 0.21/0.40  # ...number of literals in the above   : 749
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 37
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 3558
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 1723
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 72
% 0.21/0.40  # Unit Clause-clause subsumption calls : 54
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 15
% 0.21/0.40  # BW rewrite match successes           : 1
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 14023
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.049 s
% 0.21/0.40  # System time              : 0.006 s
% 0.21/0.40  # Total time               : 0.055 s
% 0.21/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
