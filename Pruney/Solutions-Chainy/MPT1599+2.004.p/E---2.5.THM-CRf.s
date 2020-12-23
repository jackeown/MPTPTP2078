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
% DateTime   : Thu Dec  3 11:15:43 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  102 (2899 expanded)
%              Number of clauses        :   71 (1179 expanded)
%              Number of leaves         :   15 ( 762 expanded)
%              Depth                    :   15
%              Number of atoms          :  428 (12117 expanded)
%              Number of equality atoms :   57 (1785 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   74 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

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

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | ~ v2_lattice3(X18)
      | ~ v2_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_17,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | m1_subset_1(k11_lattice3(X19,X20,X21),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X39] :
      ( u1_struct_0(k2_yellow_1(X39)) = X39
      & u1_orders_2(k2_yellow_1(X39)) = k1_yellow_1(X39) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_23,plain,(
    ! [X38] :
      ( v1_orders_2(k2_yellow_1(X38))
      & v3_orders_2(k2_yellow_1(X38))
      & v4_orders_2(k2_yellow_1(X38))
      & v5_orders_2(k2_yellow_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_24,plain,(
    ! [X37] :
      ( v1_orders_2(k2_yellow_1(X37))
      & l1_orders_2(k2_yellow_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v2_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_19,c_0_20])]),c_0_21])).

cnf(c_0_27,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_27]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_32,c_0_20])]),c_0_21])).

fof(c_0_39,plain,(
    ! [X28,X29,X30] :
      ( ~ v5_orders_2(X28)
      | ~ v2_lattice3(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | k12_lattice3(X28,X29,X30) = k11_lattice3(X28,X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_40,plain,(
    ! [X31,X32,X33] :
      ( ~ v5_orders_2(X31)
      | ~ v2_lattice3(X31)
      | ~ l1_orders_2(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | k11_lattice3(X31,X32,X33) = k11_lattice3(X31,X33,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

cnf(c_0_41,plain,
    ( r1_orders_2(X2,X1,X5)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X1,X4)
    | X5 != k11_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_45,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_41,c_0_20])]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_35])])).

cnf(c_0_51,plain,
    ( k12_lattice3(k2_yellow_1(X1),X2,X3) = k11_lattice3(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_52,plain,
    ( k11_lattice3(k2_yellow_1(X1),X2,X3) = k11_lattice3(k2_yellow_1(X1),X3,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_53,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0))
    | ~ r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_28]),c_0_27]),c_0_37]),c_0_27]),c_0_27]),c_0_49]),c_0_35]),c_0_29])])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),X1,esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_35])])).

cnf(c_0_57,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),esk4_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_35])])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ v5_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_53,c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_34])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_49])).

fof(c_0_62,plain,(
    ! [X34,X35,X36] :
      ( ( X35 != k12_lattice3(X34,X35,X36)
        | r3_orders_2(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | ~ v3_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ v2_lattice3(X34)
        | ~ l1_orders_2(X34) )
      & ( ~ r3_orders_2(X34,X35,X36)
        | X35 = k12_lattice3(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | ~ v3_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ v2_lattice3(X34)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).

cnf(c_0_63,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_49])).

cnf(c_0_65,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X4)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ v5_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_58,c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ r1_orders_2(k2_yellow_1(esk2_0),esk1_4(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | ~ r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_28]),c_0_27]),c_0_49]),c_0_27]),c_0_35]),c_0_29])])).

cnf(c_0_67,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_35])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

fof(c_0_69,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_70,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_71,plain,(
    ! [X40,X41,X42] :
      ( ( ~ r3_orders_2(k2_yellow_1(X40),X41,X42)
        | r1_tarski(X41,X42)
        | ~ m1_subset_1(X42,u1_struct_0(k2_yellow_1(X40)))
        | ~ m1_subset_1(X41,u1_struct_0(k2_yellow_1(X40)))
        | v1_xboole_0(X40) )
      & ( ~ r1_tarski(X41,X42)
        | r3_orders_2(k2_yellow_1(X40),X41,X42)
        | ~ m1_subset_1(X42,u1_struct_0(k2_yellow_1(X40)))
        | ~ m1_subset_1(X41,u1_struct_0(k2_yellow_1(X40)))
        | v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_72,plain,
    ( r3_orders_2(X2,X1,X3)
    | X1 != k12_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_75,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_60]),c_0_28]),c_0_27]),c_0_49]),c_0_27]),c_0_35]),c_0_29])]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),X1,esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_34]),c_0_35])])).

cnf(c_0_77,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_78,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_81,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_82,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) != k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_28]),c_0_27]),c_0_37]),c_0_27]),c_0_49]),c_0_35]),c_0_29])])).

cnf(c_0_84,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_48]),c_0_37])])).

cnf(c_0_85,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_68]),c_0_77])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_27]),c_0_27])).

cnf(c_0_90,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_92,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)
    | k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))) != k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_85]),c_0_74]),c_0_28]),c_0_27]),c_0_34]),c_0_27]),c_0_68]),c_0_35]),c_0_29])])).

cnf(c_0_93,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_55]),c_0_34])])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_37]),c_0_49])]),c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_93]),c_0_93]),c_0_93])])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(X1,X1,X1,esk4_0)))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_96]),c_0_34]),c_0_49])]),c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_87]),c_0_88])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.54/5.75  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 5.54/5.75  # and selection function SelectCQArNTNpEqFirst.
% 5.54/5.75  #
% 5.54/5.75  # Preprocessing time       : 0.029 s
% 5.54/5.75  # Presaturation interreduction done
% 5.54/5.75  
% 5.54/5.75  # Proof found!
% 5.54/5.75  # SZS status Theorem
% 5.54/5.75  # SZS output start CNFRefutation
% 5.54/5.75  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 5.54/5.75  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 5.54/5.75  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 5.54/5.75  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 5.54/5.75  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 5.54/5.75  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 5.54/5.75  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 5.54/5.75  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 5.54/5.75  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 5.54/5.75  fof(t25_yellow_0, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k12_lattice3(X1,X2,X3)<=>r3_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 5.54/5.75  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.54/5.75  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.54/5.75  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 5.54/5.75  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.54/5.75  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.54/5.75  fof(c_0_15, plain, ![X22, X23, X24, X25, X26]:((((r1_orders_2(X22,X25,X23)|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,X25,X24)|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&(~m1_subset_1(X26,u1_struct_0(X22))|(~r1_orders_2(X22,X26,X23)|~r1_orders_2(X22,X26,X24)|r1_orders_2(X22,X26,X25))|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&((m1_subset_1(esk1_4(X22,X23,X24,X25),u1_struct_0(X22))|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(((r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X23)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X24)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&(~r1_orders_2(X22,esk1_4(X22,X23,X24,X25),X25)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 5.54/5.75  fof(c_0_16, plain, ![X18]:(~l1_orders_2(X18)|(~v2_lattice3(X18)|~v2_struct_0(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 5.54/5.75  fof(c_0_17, plain, ![X19, X20, X21]:(~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|m1_subset_1(k11_lattice3(X19,X20,X21),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 5.54/5.75  fof(c_0_18, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 5.54/5.75  cnf(c_0_19, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.54/5.75  cnf(c_0_20, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.54/5.75  cnf(c_0_21, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.54/5.75  fof(c_0_22, plain, ![X39]:(u1_struct_0(k2_yellow_1(X39))=X39&u1_orders_2(k2_yellow_1(X39))=k1_yellow_1(X39)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 5.54/5.75  fof(c_0_23, plain, ![X38]:(((v1_orders_2(k2_yellow_1(X38))&v3_orders_2(k2_yellow_1(X38)))&v4_orders_2(k2_yellow_1(X38)))&v5_orders_2(k2_yellow_1(X38))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 5.54/5.75  fof(c_0_24, plain, ![X37]:(v1_orders_2(k2_yellow_1(X37))&l1_orders_2(k2_yellow_1(X37))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 5.54/5.75  fof(c_0_25, negated_conjecture, (~v1_xboole_0(esk2_0)&(v2_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 5.54/5.75  cnf(c_0_26, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_19, c_0_20])]), c_0_21])).
% 5.54/5.75  cnf(c_0_27, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.54/5.75  cnf(c_0_28, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.54/5.75  cnf(c_0_29, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.54/5.75  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.54/5.75  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.54/5.75  cnf(c_0_32, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X3,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.54/5.75  cnf(c_0_33, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 5.54/5.75  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_30, c_0_27])).
% 5.54/5.75  cnf(c_0_35, negated_conjecture, (v2_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.54/5.75  cnf(c_0_36, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_27]), c_0_29])])).
% 5.54/5.75  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_31, c_0_27])).
% 5.54/5.75  cnf(c_0_38, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_32, c_0_20])]), c_0_21])).
% 5.54/5.75  fof(c_0_39, plain, ![X28, X29, X30]:(~v5_orders_2(X28)|~v2_lattice3(X28)|~l1_orders_2(X28)|~m1_subset_1(X29,u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X28))|k12_lattice3(X28,X29,X30)=k11_lattice3(X28,X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 5.54/5.75  fof(c_0_40, plain, ![X31, X32, X33]:(~v5_orders_2(X31)|~v2_lattice3(X31)|~l1_orders_2(X31)|(~m1_subset_1(X32,u1_struct_0(X31))|(~m1_subset_1(X33,u1_struct_0(X31))|k11_lattice3(X31,X32,X33)=k11_lattice3(X31,X33,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 5.54/5.75  cnf(c_0_41, plain, (r1_orders_2(X2,X1,X5)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X1,X3)|~r1_orders_2(X2,X1,X4)|X5!=k11_lattice3(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.54/5.75  cnf(c_0_42, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 5.54/5.75  cnf(c_0_43, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 5.54/5.75  cnf(c_0_44, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_27]), c_0_28]), c_0_29])])).
% 5.54/5.75  cnf(c_0_45, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 5.54/5.75  cnf(c_0_46, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.54/5.75  cnf(c_0_47, plain, (r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X2,X3)|~v5_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_41, c_0_20])]), c_0_21])).
% 5.54/5.75  cnf(c_0_48, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 5.54/5.75  cnf(c_0_49, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_34])).
% 5.54/5.75  cnf(c_0_50, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_35])])).
% 5.54/5.75  cnf(c_0_51, plain, (k12_lattice3(k2_yellow_1(X1),X2,X3)=k11_lattice3(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_28]), c_0_29])])).
% 5.54/5.75  cnf(c_0_52, plain, (k11_lattice3(k2_yellow_1(X1),X2,X3)=k11_lattice3(k2_yellow_1(X1),X3,X2)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_28]), c_0_29])])).
% 5.54/5.75  cnf(c_0_53, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.54/5.75  cnf(c_0_54, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0))|~r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_28]), c_0_27]), c_0_37]), c_0_27]), c_0_27]), c_0_49]), c_0_35]), c_0_29])])).
% 5.54/5.75  cnf(c_0_55, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_34])).
% 5.54/5.75  cnf(c_0_56, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_37]), c_0_35])])).
% 5.54/5.75  cnf(c_0_57, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),esk4_0,X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_37]), c_0_35])])).
% 5.54/5.75  cnf(c_0_58, plain, (r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X3)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.54/5.75  cnf(c_0_59, plain, (X1=k11_lattice3(X2,X3,X4)|~r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X1)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_53, c_0_20])).
% 5.54/5.75  cnf(c_0_60, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_34])])).
% 5.54/5.75  cnf(c_0_61, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_49])).
% 5.54/5.75  fof(c_0_62, plain, ![X34, X35, X36]:((X35!=k12_lattice3(X34,X35,X36)|r3_orders_2(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(~v3_orders_2(X34)|~v5_orders_2(X34)|~v2_lattice3(X34)|~l1_orders_2(X34)))&(~r3_orders_2(X34,X35,X36)|X35=k12_lattice3(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(~v3_orders_2(X34)|~v5_orders_2(X34)|~v2_lattice3(X34)|~l1_orders_2(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).
% 5.54/5.75  cnf(c_0_63, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_49])).
% 5.54/5.75  cnf(c_0_64, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_49])).
% 5.54/5.75  cnf(c_0_65, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X4)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_58, c_0_20])).
% 5.54/5.75  cnf(c_0_66, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~r1_orders_2(k2_yellow_1(esk2_0),esk1_4(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|~r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_28]), c_0_27]), c_0_49]), c_0_27]), c_0_35]), c_0_29])])).
% 5.54/5.75  cnf(c_0_67, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_34]), c_0_35])])).
% 5.54/5.75  cnf(c_0_68, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 5.54/5.75  fof(c_0_69, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 5.54/5.75  fof(c_0_70, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.54/5.75  fof(c_0_71, plain, ![X40, X41, X42]:((~r3_orders_2(k2_yellow_1(X40),X41,X42)|r1_tarski(X41,X42)|~m1_subset_1(X42,u1_struct_0(k2_yellow_1(X40)))|~m1_subset_1(X41,u1_struct_0(k2_yellow_1(X40)))|v1_xboole_0(X40))&(~r1_tarski(X41,X42)|r3_orders_2(k2_yellow_1(X40),X41,X42)|~m1_subset_1(X42,u1_struct_0(k2_yellow_1(X40)))|~m1_subset_1(X41,u1_struct_0(k2_yellow_1(X40)))|v1_xboole_0(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 5.54/5.75  cnf(c_0_72, plain, (r3_orders_2(X2,X1,X3)|X1!=k12_lattice3(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 5.54/5.75  cnf(c_0_73, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 5.54/5.75  cnf(c_0_74, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.54/5.75  cnf(c_0_75, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_60]), c_0_28]), c_0_27]), c_0_49]), c_0_27]), c_0_35]), c_0_29])]), c_0_66])).
% 5.54/5.75  cnf(c_0_76, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_34]), c_0_35])])).
% 5.54/5.75  cnf(c_0_77, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 5.54/5.75  fof(c_0_78, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 5.54/5.75  cnf(c_0_79, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 5.54/5.75  cnf(c_0_80, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 5.54/5.75  fof(c_0_81, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 5.54/5.75  cnf(c_0_82, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 5.54/5.75  cnf(c_0_83, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))!=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_28]), c_0_27]), c_0_37]), c_0_27]), c_0_49]), c_0_35]), c_0_29])])).
% 5.54/5.75  cnf(c_0_84, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_48]), c_0_37])])).
% 5.54/5.75  cnf(c_0_85, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_68]), c_0_77])).
% 5.54/5.75  cnf(c_0_86, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 5.54/5.75  cnf(c_0_87, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 5.54/5.75  cnf(c_0_88, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 5.54/5.75  cnf(c_0_89, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_27]), c_0_27])).
% 5.54/5.75  cnf(c_0_90, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 5.54/5.75  cnf(c_0_91, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.54/5.75  cnf(c_0_92, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)|k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))!=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_85]), c_0_74]), c_0_28]), c_0_27]), c_0_34]), c_0_27]), c_0_68]), c_0_35]), c_0_29])])).
% 5.54/5.75  cnf(c_0_93, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_55]), c_0_34])])).
% 5.54/5.75  cnf(c_0_94, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 5.54/5.75  cnf(c_0_95, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_37]), c_0_49])]), c_0_91])).
% 5.54/5.75  cnf(c_0_96, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_93]), c_0_93]), c_0_93])])).
% 5.54/5.75  cnf(c_0_97, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.54/5.75  cnf(c_0_98, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(X1,X1,X1,esk4_0)))|~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 5.54/5.75  cnf(c_0_99, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_96]), c_0_34]), c_0_49])]), c_0_91])).
% 5.54/5.75  cnf(c_0_100, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_87]), c_0_88])).
% 5.54/5.75  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), ['proof']).
% 5.54/5.75  # SZS output end CNFRefutation
% 5.54/5.75  # Proof object total steps             : 102
% 5.54/5.75  # Proof object clause steps            : 71
% 5.54/5.75  # Proof object formula steps           : 31
% 5.54/5.75  # Proof object conjectures             : 42
% 5.54/5.75  # Proof object clause conjectures      : 39
% 5.54/5.75  # Proof object formula conjectures     : 3
% 5.54/5.75  # Proof object initial clauses used    : 24
% 5.54/5.75  # Proof object initial formulas used   : 15
% 5.54/5.75  # Proof object generating inferences   : 33
% 5.54/5.75  # Proof object simplifying inferences  : 112
% 5.54/5.75  # Training examples: 0 positive, 0 negative
% 5.54/5.75  # Parsed axioms                        : 16
% 5.54/5.75  # Removed by relevancy pruning/SinE    : 0
% 5.54/5.75  # Initial clauses                      : 35
% 5.54/5.75  # Removed in clause preprocessing      : 4
% 5.54/5.75  # Initial clauses in saturation        : 31
% 5.54/5.75  # Processed clauses                    : 3288
% 5.54/5.75  # ...of these trivial                  : 90
% 5.54/5.75  # ...subsumed                          : 679
% 5.54/5.75  # ...remaining for further processing  : 2519
% 5.54/5.75  # Other redundant clauses eliminated   : 5
% 5.54/5.75  # Clauses deleted for lack of memory   : 0
% 5.54/5.75  # Backward-subsumed                    : 8
% 5.54/5.75  # Backward-rewritten                   : 2139
% 5.54/5.75  # Generated clauses                    : 705920
% 5.54/5.75  # ...of the previous two non-trivial   : 706806
% 5.54/5.75  # Contextual simplify-reflections      : 13
% 5.54/5.75  # Paramodulations                      : 705915
% 5.54/5.75  # Factorizations                       : 0
% 5.54/5.75  # Equation resolutions                 : 5
% 5.54/5.75  # Propositional unsat checks           : 0
% 5.54/5.75  #    Propositional check models        : 0
% 5.54/5.75  #    Propositional check unsatisfiable : 0
% 5.54/5.75  #    Propositional clauses             : 0
% 5.54/5.75  #    Propositional clauses after purity: 0
% 5.54/5.75  #    Propositional unsat core size     : 0
% 5.54/5.75  #    Propositional preprocessing time  : 0.000
% 5.54/5.75  #    Propositional encoding time       : 0.000
% 5.54/5.75  #    Propositional solver time         : 0.000
% 5.54/5.75  #    Success case prop preproc time    : 0.000
% 5.54/5.75  #    Success case prop encoding time   : 0.000
% 5.54/5.75  #    Success case prop solver time     : 0.000
% 5.54/5.75  # Current number of processed clauses  : 338
% 5.54/5.75  #    Positive orientable unit clauses  : 47
% 5.54/5.75  #    Positive unorientable unit clauses: 0
% 5.54/5.75  #    Negative unit clauses             : 2
% 5.54/5.75  #    Non-unit-clauses                  : 289
% 5.54/5.75  # Current number of unprocessed clauses: 697400
% 5.54/5.75  # ...number of literals in the above   : 931180
% 5.54/5.75  # Current number of archived formulas  : 0
% 5.54/5.75  # Current number of archived clauses   : 2180
% 5.54/5.75  # Clause-clause subsumption calls (NU) : 191838
% 5.54/5.75  # Rec. Clause-clause subsumption calls : 182715
% 5.54/5.75  # Non-unit clause-clause subsumptions  : 700
% 5.54/5.75  # Unit Clause-clause subsumption calls : 14052
% 5.54/5.75  # Rewrite failures with RHS unbound    : 0
% 5.54/5.75  # BW rewrite match attempts            : 195980
% 5.54/5.75  # BW rewrite match successes           : 25
% 5.54/5.75  # Condensation attempts                : 0
% 5.54/5.75  # Condensation successes               : 0
% 5.54/5.75  # Termbank termtop insertions          : 52834649
% 5.54/5.78  
% 5.54/5.78  # -------------------------------------------------
% 5.54/5.78  # User time                : 5.112 s
% 5.54/5.78  # System time              : 0.297 s
% 5.54/5.78  # Total time               : 5.409 s
% 5.54/5.78  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
