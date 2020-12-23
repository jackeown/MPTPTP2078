%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:43 EST 2020

% Result     : Theorem 5.67s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   98 (2891 expanded)
%              Number of clauses        :   69 (1175 expanded)
%              Number of leaves         :   14 ( 760 expanded)
%              Depth                    :   15
%              Number of atoms          :  424 (12109 expanded)
%              Number of equality atoms :   53 (1777 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

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

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

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

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

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

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(c_0_14,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( r1_orders_2(X19,X22,X20)
        | X22 != k11_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v2_lattice3(X19)
        | ~ l1_orders_2(X19) )
      & ( r1_orders_2(X19,X22,X21)
        | X22 != k11_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v2_lattice3(X19)
        | ~ l1_orders_2(X19) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X19))
        | ~ r1_orders_2(X19,X23,X20)
        | ~ r1_orders_2(X19,X23,X21)
        | r1_orders_2(X19,X23,X22)
        | X22 != k11_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v2_lattice3(X19)
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk1_4(X19,X20,X21,X22),u1_struct_0(X19))
        | ~ r1_orders_2(X19,X22,X20)
        | ~ r1_orders_2(X19,X22,X21)
        | X22 = k11_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v2_lattice3(X19)
        | ~ l1_orders_2(X19) )
      & ( r1_orders_2(X19,esk1_4(X19,X20,X21,X22),X20)
        | ~ r1_orders_2(X19,X22,X20)
        | ~ r1_orders_2(X19,X22,X21)
        | X22 = k11_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v2_lattice3(X19)
        | ~ l1_orders_2(X19) )
      & ( r1_orders_2(X19,esk1_4(X19,X20,X21,X22),X21)
        | ~ r1_orders_2(X19,X22,X20)
        | ~ r1_orders_2(X19,X22,X21)
        | X22 = k11_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v2_lattice3(X19)
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,esk1_4(X19,X20,X21,X22),X22)
        | ~ r1_orders_2(X19,X22,X20)
        | ~ r1_orders_2(X19,X22,X21)
        | X22 = k11_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v2_lattice3(X19)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_15,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | ~ v2_lattice3(X15)
      | ~ v2_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

cnf(c_0_18,plain,
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

cnf(c_0_19,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X36] :
      ( u1_struct_0(k2_yellow_1(X36)) = X36
      & u1_orders_2(k2_yellow_1(X36)) = k1_yellow_1(X36) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_22,plain,(
    ! [X35] :
      ( v1_orders_2(k2_yellow_1(X35))
      & v3_orders_2(k2_yellow_1(X35))
      & v4_orders_2(k2_yellow_1(X35))
      & v5_orders_2(k2_yellow_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_23,plain,(
    ! [X34] :
      ( v1_orders_2(k2_yellow_1(X34))
      & l1_orders_2(k2_yellow_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v2_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_18,c_0_19])]),c_0_20])).

cnf(c_0_26,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
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

cnf(c_0_32,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_19])]),c_0_20])).

fof(c_0_38,plain,(
    ! [X25,X26,X27] :
      ( ~ v5_orders_2(X25)
      | ~ v2_lattice3(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | k12_lattice3(X25,X26,X27) = k11_lattice3(X25,X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_39,plain,(
    ! [X28,X29,X30] :
      ( ~ v5_orders_2(X28)
      | ~ v2_lattice3(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | k11_lattice3(X28,X29,X30) = k11_lattice3(X28,X30,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_44,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_40,c_0_19])]),c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_34])])).

cnf(c_0_50,plain,
    ( k12_lattice3(k2_yellow_1(X1),X2,X3) = k11_lattice3(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_51,plain,
    ( k11_lattice3(k2_yellow_1(X1),X2,X3) = k11_lattice3(k2_yellow_1(X1),X3,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0))
    | ~ r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_27]),c_0_26]),c_0_36]),c_0_26]),c_0_26]),c_0_48]),c_0_34]),c_0_28])])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),X1,esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_36]),c_0_34])])).

cnf(c_0_56,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),esk4_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_36]),c_0_34])])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,plain,
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
    inference(csr,[status(thm)],[c_0_52,c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_33])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_48])).

fof(c_0_61,plain,(
    ! [X31,X32,X33] :
      ( ( X32 != k12_lattice3(X31,X32,X33)
        | r3_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) )
      & ( ~ r3_orders_2(X31,X32,X33)
        | X32 = k12_lattice3(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).

cnf(c_0_62,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_48])).

cnf(c_0_64,plain,
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
    inference(csr,[status(thm)],[c_0_57,c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ r1_orders_2(k2_yellow_1(esk2_0),esk1_4(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | ~ r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_27]),c_0_26]),c_0_48]),c_0_26]),c_0_34]),c_0_28])])).

cnf(c_0_66,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_34])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_33])).

fof(c_0_68,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r3_orders_2(k2_yellow_1(X37),X38,X39)
        | r1_tarski(X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(k2_yellow_1(X37)))
        | ~ m1_subset_1(X38,u1_struct_0(k2_yellow_1(X37)))
        | v1_xboole_0(X37) )
      & ( ~ r1_tarski(X38,X39)
        | r3_orders_2(k2_yellow_1(X37),X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(k2_yellow_1(X37)))
        | ~ m1_subset_1(X38,u1_struct_0(k2_yellow_1(X37)))
        | v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_69,plain,
    ( r3_orders_2(X2,X1,X3)
    | X1 != k12_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_72,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_59]),c_0_27]),c_0_26]),c_0_48]),c_0_26]),c_0_34]),c_0_28])]),c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),X1,esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_34])])).

cnf(c_0_74,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_75,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_76,plain,(
    ! [X13,X14] : k1_setfam_1(k2_tarski(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_77,plain,(
    ! [X11,X12] : k2_enumset1(X11,X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

cnf(c_0_78,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) != k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_27]),c_0_26]),c_0_36]),c_0_26]),c_0_48]),c_0_34]),c_0_28])])).

cnf(c_0_80,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_47]),c_0_36])])).

cnf(c_0_81,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_67]),c_0_74])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_26]),c_0_26])).

cnf(c_0_86,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)
    | k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))) != k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_81]),c_0_71]),c_0_27]),c_0_26]),c_0_33]),c_0_26]),c_0_67]),c_0_34]),c_0_28])])).

cnf(c_0_89,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_33])])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_36]),c_0_48])]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_89]),c_0_89]),c_0_89])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(X1,X1,X1,esk4_0)))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_92]),c_0_33]),c_0_48])]),c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_83]),c_0_84])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 5.67/5.89  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 5.67/5.89  # and selection function SelectCQArNTNpEqFirst.
% 5.67/5.89  #
% 5.67/5.89  # Preprocessing time       : 0.029 s
% 5.67/5.89  # Presaturation interreduction done
% 5.67/5.89  
% 5.67/5.89  # Proof found!
% 5.67/5.89  # SZS status Theorem
% 5.67/5.89  # SZS output start CNFRefutation
% 5.67/5.89  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 5.67/5.89  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 5.67/5.89  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 5.67/5.89  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 5.67/5.89  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 5.67/5.89  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 5.67/5.89  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 5.67/5.89  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 5.67/5.89  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 5.67/5.89  fof(t25_yellow_0, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k12_lattice3(X1,X2,X3)<=>r3_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_0)).
% 5.67/5.89  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 5.67/5.89  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.67/5.89  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.67/5.89  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 5.67/5.89  fof(c_0_14, plain, ![X19, X20, X21, X22, X23]:((((r1_orders_2(X19,X22,X20)|X22!=k11_lattice3(X19,X20,X21)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19)))&(r1_orders_2(X19,X22,X21)|X22!=k11_lattice3(X19,X20,X21)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19))))&(~m1_subset_1(X23,u1_struct_0(X19))|(~r1_orders_2(X19,X23,X20)|~r1_orders_2(X19,X23,X21)|r1_orders_2(X19,X23,X22))|X22!=k11_lattice3(X19,X20,X21)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19))))&((m1_subset_1(esk1_4(X19,X20,X21,X22),u1_struct_0(X19))|(~r1_orders_2(X19,X22,X20)|~r1_orders_2(X19,X22,X21))|X22=k11_lattice3(X19,X20,X21)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19)))&(((r1_orders_2(X19,esk1_4(X19,X20,X21,X22),X20)|(~r1_orders_2(X19,X22,X20)|~r1_orders_2(X19,X22,X21))|X22=k11_lattice3(X19,X20,X21)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19)))&(r1_orders_2(X19,esk1_4(X19,X20,X21,X22),X21)|(~r1_orders_2(X19,X22,X20)|~r1_orders_2(X19,X22,X21))|X22=k11_lattice3(X19,X20,X21)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19))))&(~r1_orders_2(X19,esk1_4(X19,X20,X21,X22),X22)|(~r1_orders_2(X19,X22,X20)|~r1_orders_2(X19,X22,X21))|X22=k11_lattice3(X19,X20,X21)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 5.67/5.89  fof(c_0_15, plain, ![X15]:(~l1_orders_2(X15)|(~v2_lattice3(X15)|~v2_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 5.67/5.89  fof(c_0_16, plain, ![X16, X17, X18]:(~l1_orders_2(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 5.67/5.89  fof(c_0_17, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 5.67/5.89  cnf(c_0_18, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.67/5.89  cnf(c_0_19, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.67/5.89  cnf(c_0_20, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.67/5.89  fof(c_0_21, plain, ![X36]:(u1_struct_0(k2_yellow_1(X36))=X36&u1_orders_2(k2_yellow_1(X36))=k1_yellow_1(X36)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 5.67/5.89  fof(c_0_22, plain, ![X35]:(((v1_orders_2(k2_yellow_1(X35))&v3_orders_2(k2_yellow_1(X35)))&v4_orders_2(k2_yellow_1(X35)))&v5_orders_2(k2_yellow_1(X35))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 5.67/5.89  fof(c_0_23, plain, ![X34]:(v1_orders_2(k2_yellow_1(X34))&l1_orders_2(k2_yellow_1(X34))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 5.67/5.89  fof(c_0_24, negated_conjecture, (~v1_xboole_0(esk2_0)&(v2_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 5.67/5.89  cnf(c_0_25, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_18, c_0_19])]), c_0_20])).
% 5.67/5.89  cnf(c_0_26, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.67/5.89  cnf(c_0_27, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.67/5.89  cnf(c_0_28, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.67/5.89  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.67/5.89  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.67/5.89  cnf(c_0_31, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X3,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.67/5.89  cnf(c_0_32, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 5.67/5.89  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_29, c_0_26])).
% 5.67/5.89  cnf(c_0_34, negated_conjecture, (v2_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.67/5.89  cnf(c_0_35, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_28])])).
% 5.67/5.89  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_30, c_0_26])).
% 5.67/5.89  cnf(c_0_37, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31, c_0_19])]), c_0_20])).
% 5.67/5.89  fof(c_0_38, plain, ![X25, X26, X27]:(~v5_orders_2(X25)|~v2_lattice3(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|k12_lattice3(X25,X26,X27)=k11_lattice3(X25,X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 5.67/5.89  fof(c_0_39, plain, ![X28, X29, X30]:(~v5_orders_2(X28)|~v2_lattice3(X28)|~l1_orders_2(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|(~m1_subset_1(X30,u1_struct_0(X28))|k11_lattice3(X28,X29,X30)=k11_lattice3(X28,X30,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 5.67/5.89  cnf(c_0_40, plain, (r1_orders_2(X2,X1,X5)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X1,X3)|~r1_orders_2(X2,X1,X4)|X5!=k11_lattice3(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.67/5.89  cnf(c_0_41, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 5.67/5.89  cnf(c_0_42, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 5.67/5.89  cnf(c_0_43, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_27]), c_0_28])])).
% 5.67/5.89  cnf(c_0_44, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 5.67/5.89  cnf(c_0_45, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 5.67/5.89  cnf(c_0_46, plain, (r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X2,X3)|~v5_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_40, c_0_19])]), c_0_20])).
% 5.67/5.89  cnf(c_0_47, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 5.67/5.89  cnf(c_0_48, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 5.67/5.89  cnf(c_0_49, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_36]), c_0_34])])).
% 5.67/5.89  cnf(c_0_50, plain, (k12_lattice3(k2_yellow_1(X1),X2,X3)=k11_lattice3(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_26]), c_0_27]), c_0_28])])).
% 5.67/5.89  cnf(c_0_51, plain, (k11_lattice3(k2_yellow_1(X1),X2,X3)=k11_lattice3(k2_yellow_1(X1),X3,X2)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~v2_lattice3(k2_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_27]), c_0_28])])).
% 5.67/5.89  cnf(c_0_52, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.67/5.89  cnf(c_0_53, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0))|~r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_27]), c_0_26]), c_0_36]), c_0_26]), c_0_26]), c_0_48]), c_0_34]), c_0_28])])).
% 5.67/5.89  cnf(c_0_54, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_33])).
% 5.67/5.89  cnf(c_0_55, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_36]), c_0_34])])).
% 5.67/5.89  cnf(c_0_56, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),esk4_0,X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_36]), c_0_34])])).
% 5.67/5.89  cnf(c_0_57, plain, (r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X3)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.67/5.89  cnf(c_0_58, plain, (X1=k11_lattice3(X2,X3,X4)|~r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X1)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_52, c_0_19])).
% 5.67/5.89  cnf(c_0_59, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_33])])).
% 5.67/5.89  cnf(c_0_60, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_48])).
% 5.67/5.89  fof(c_0_61, plain, ![X31, X32, X33]:((X32!=k12_lattice3(X31,X32,X33)|r3_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v5_orders_2(X31)|~v2_lattice3(X31)|~l1_orders_2(X31)))&(~r3_orders_2(X31,X32,X33)|X32=k12_lattice3(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v5_orders_2(X31)|~v2_lattice3(X31)|~l1_orders_2(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).
% 5.67/5.89  cnf(c_0_62, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_48])).
% 5.67/5.89  cnf(c_0_63, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_48])).
% 5.67/5.89  cnf(c_0_64, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X4)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_57, c_0_19])).
% 5.67/5.89  cnf(c_0_65, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~r1_orders_2(k2_yellow_1(esk2_0),esk1_4(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|~r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_27]), c_0_26]), c_0_48]), c_0_26]), c_0_34]), c_0_28])])).
% 5.67/5.89  cnf(c_0_66, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_33]), c_0_34])])).
% 5.67/5.89  cnf(c_0_67, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_33])).
% 5.67/5.89  fof(c_0_68, plain, ![X37, X38, X39]:((~r3_orders_2(k2_yellow_1(X37),X38,X39)|r1_tarski(X38,X39)|~m1_subset_1(X39,u1_struct_0(k2_yellow_1(X37)))|~m1_subset_1(X38,u1_struct_0(k2_yellow_1(X37)))|v1_xboole_0(X37))&(~r1_tarski(X38,X39)|r3_orders_2(k2_yellow_1(X37),X38,X39)|~m1_subset_1(X39,u1_struct_0(k2_yellow_1(X37)))|~m1_subset_1(X38,u1_struct_0(k2_yellow_1(X37)))|v1_xboole_0(X37))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 5.67/5.89  cnf(c_0_69, plain, (r3_orders_2(X2,X1,X3)|X1!=k12_lattice3(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 5.67/5.89  cnf(c_0_70, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 5.67/5.89  cnf(c_0_71, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.67/5.89  cnf(c_0_72, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),X1,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)|~m1_subset_1(X1,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_59]), c_0_27]), c_0_26]), c_0_48]), c_0_26]), c_0_34]), c_0_28])]), c_0_65])).
% 5.67/5.89  cnf(c_0_73, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),X1,esk3_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_33]), c_0_34])])).
% 5.67/5.89  cnf(c_0_74, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 5.67/5.89  fof(c_0_75, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 5.67/5.89  fof(c_0_76, plain, ![X13, X14]:k1_setfam_1(k2_tarski(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 5.67/5.89  fof(c_0_77, plain, ![X11, X12]:k2_enumset1(X11,X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 5.67/5.89  cnf(c_0_78, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 5.67/5.89  cnf(c_0_79, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))!=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_27]), c_0_26]), c_0_36]), c_0_26]), c_0_48]), c_0_34]), c_0_28])])).
% 5.67/5.89  cnf(c_0_80, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),esk4_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_47]), c_0_36])])).
% 5.67/5.89  cnf(c_0_81, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_67]), c_0_74])).
% 5.67/5.89  cnf(c_0_82, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 5.67/5.89  cnf(c_0_83, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 5.67/5.89  cnf(c_0_84, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 5.67/5.89  cnf(c_0_85, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_26]), c_0_26])).
% 5.67/5.89  cnf(c_0_86, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 5.67/5.89  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.67/5.89  cnf(c_0_88, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)),esk3_0)|k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))!=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_81]), c_0_71]), c_0_27]), c_0_26]), c_0_33]), c_0_26]), c_0_67]), c_0_34]), c_0_28])])).
% 5.67/5.89  cnf(c_0_89, negated_conjecture, (k11_lattice3(k2_yellow_1(esk2_0),esk3_0,k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_54]), c_0_33])])).
% 5.67/5.89  cnf(c_0_90, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 5.67/5.89  cnf(c_0_91, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_36]), c_0_48])]), c_0_87])).
% 5.67/5.89  cnf(c_0_92, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_89]), c_0_89]), c_0_89])])).
% 5.67/5.89  cnf(c_0_93, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.67/5.89  cnf(c_0_94, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(X1,X1,X1,esk4_0)))|~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 5.67/5.89  cnf(c_0_95, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_92]), c_0_33]), c_0_48])]), c_0_87])).
% 5.67/5.89  cnf(c_0_96, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_83]), c_0_84])).
% 5.67/5.89  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), ['proof']).
% 5.67/5.89  # SZS output end CNFRefutation
% 5.67/5.89  # Proof object total steps             : 98
% 5.67/5.89  # Proof object clause steps            : 69
% 5.67/5.89  # Proof object formula steps           : 29
% 5.67/5.89  # Proof object conjectures             : 42
% 5.67/5.89  # Proof object clause conjectures      : 39
% 5.67/5.89  # Proof object formula conjectures     : 3
% 5.67/5.89  # Proof object initial clauses used    : 23
% 5.67/5.89  # Proof object initial formulas used   : 14
% 5.67/5.89  # Proof object generating inferences   : 33
% 5.67/5.89  # Proof object simplifying inferences  : 111
% 5.67/5.89  # Training examples: 0 positive, 0 negative
% 5.67/5.89  # Parsed axioms                        : 15
% 5.67/5.89  # Removed by relevancy pruning/SinE    : 0
% 5.67/5.89  # Initial clauses                      : 34
% 5.67/5.89  # Removed in clause preprocessing      : 3
% 5.67/5.89  # Initial clauses in saturation        : 31
% 5.67/5.89  # Processed clauses                    : 3288
% 5.67/5.89  # ...of these trivial                  : 90
% 5.67/5.89  # ...subsumed                          : 679
% 5.67/5.89  # ...remaining for further processing  : 2519
% 5.67/5.89  # Other redundant clauses eliminated   : 5
% 5.67/5.89  # Clauses deleted for lack of memory   : 0
% 5.67/5.89  # Backward-subsumed                    : 8
% 5.67/5.89  # Backward-rewritten                   : 2139
% 5.67/5.89  # Generated clauses                    : 705920
% 5.67/5.89  # ...of the previous two non-trivial   : 706806
% 5.67/5.89  # Contextual simplify-reflections      : 13
% 5.67/5.89  # Paramodulations                      : 705915
% 5.67/5.89  # Factorizations                       : 0
% 5.67/5.89  # Equation resolutions                 : 5
% 5.67/5.89  # Propositional unsat checks           : 0
% 5.67/5.89  #    Propositional check models        : 0
% 5.67/5.89  #    Propositional check unsatisfiable : 0
% 5.67/5.89  #    Propositional clauses             : 0
% 5.67/5.89  #    Propositional clauses after purity: 0
% 5.67/5.89  #    Propositional unsat core size     : 0
% 5.67/5.89  #    Propositional preprocessing time  : 0.000
% 5.67/5.89  #    Propositional encoding time       : 0.000
% 5.67/5.89  #    Propositional solver time         : 0.000
% 5.67/5.89  #    Success case prop preproc time    : 0.000
% 5.67/5.89  #    Success case prop encoding time   : 0.000
% 5.67/5.89  #    Success case prop solver time     : 0.000
% 5.67/5.89  # Current number of processed clauses  : 338
% 5.67/5.89  #    Positive orientable unit clauses  : 47
% 5.67/5.89  #    Positive unorientable unit clauses: 0
% 5.67/5.89  #    Negative unit clauses             : 2
% 5.67/5.89  #    Non-unit-clauses                  : 289
% 5.67/5.89  # Current number of unprocessed clauses: 697400
% 5.67/5.89  # ...number of literals in the above   : 931180
% 5.67/5.89  # Current number of archived formulas  : 0
% 5.67/5.89  # Current number of archived clauses   : 2179
% 5.67/5.89  # Clause-clause subsumption calls (NU) : 303747
% 5.67/5.89  # Rec. Clause-clause subsumption calls : 291544
% 5.67/5.89  # Non-unit clause-clause subsumptions  : 700
% 5.67/5.89  # Unit Clause-clause subsumption calls : 91067
% 5.67/5.89  # Rewrite failures with RHS unbound    : 0
% 5.67/5.89  # BW rewrite match attempts            : 195980
% 5.67/5.89  # BW rewrite match successes           : 25
% 5.67/5.89  # Condensation attempts                : 0
% 5.67/5.89  # Condensation successes               : 0
% 5.67/5.89  # Termbank termtop insertions          : 52834615
% 5.74/5.92  
% 5.74/5.92  # -------------------------------------------------
% 5.74/5.92  # User time                : 5.265 s
% 5.74/5.92  # System time              : 0.315 s
% 5.74/5.92  # Total time               : 5.581 s
% 5.74/5.92  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
