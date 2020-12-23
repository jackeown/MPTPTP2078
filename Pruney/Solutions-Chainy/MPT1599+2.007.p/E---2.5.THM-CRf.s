%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:43 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 228 expanded)
%              Number of clauses        :   37 (  93 expanded)
%              Number of leaves         :   10 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  302 ( 875 expanded)
%              Number of equality atoms :   19 ( 112 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   74 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

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

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( r1_orders_2(X16,X19,X17)
        | X19 != k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X19,X18)
        | X19 != k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X16))
        | ~ r1_orders_2(X16,X20,X17)
        | ~ r1_orders_2(X16,X20,X18)
        | r1_orders_2(X16,X20,X19)
        | X19 != k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_4(X16,X17,X18,X19),u1_struct_0(X16))
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X17)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X18)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X19)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_11,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | ~ v2_lattice3(X12)
      | ~ v2_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X25] :
      ( u1_struct_0(k2_yellow_1(X25)) = X25
      & u1_orders_2(k2_yellow_1(X25)) = k1_yellow_1(X25) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_15,plain,(
    ! [X23] :
      ( v1_orders_2(k2_yellow_1(X23))
      & v3_orders_2(k2_yellow_1(X23))
      & v4_orders_2(k2_yellow_1(X23))
      & v5_orders_2(k2_yellow_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_16,plain,(
    ! [X22] :
      ( v1_orders_2(k2_yellow_1(X22))
      & l1_orders_2(k2_yellow_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_17,plain,(
    ! [X13,X14,X15] :
      ( ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | m1_subset_1(k11_lattice3(X13,X14,X15),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_18,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r3_orders_2(X9,X10,X11)
        | r1_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) )
      & ( ~ r1_orders_2(X9,X10,X11)
        | r3_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | X2 != k11_lattice3(k2_yellow_1(X1),X4,X3)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_22])])).

fof(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v2_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_25,c_0_13])).

fof(c_0_32,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r3_orders_2(k2_yellow_1(X26),X27,X28)
        | r1_tarski(X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(k2_yellow_1(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(k2_yellow_1(X26)))
        | v1_xboole_0(X26) )
      & ( ~ r1_tarski(X27,X28)
        | r3_orders_2(k2_yellow_1(X26),X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(k2_yellow_1(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(k2_yellow_1(X26)))
        | v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_33,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_22]),c_0_27])])).

cnf(c_0_34,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | X2 != k11_lattice3(k2_yellow_1(X1),X3,X4)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_21]),c_0_22])])).

fof(c_0_37,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_35]),c_0_22])])).

cnf(c_0_41,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_20]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,plain,
    ( r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_41]),c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_46]),c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_53]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:36:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.21/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.029 s
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 0.21/0.40  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.21/0.40  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.21/0.40  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.21/0.40  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.21/0.40  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.21/0.40  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.21/0.40  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.21/0.40  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.21/0.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.21/0.40  fof(c_0_10, plain, ![X16, X17, X18, X19, X20]:((((r1_orders_2(X16,X19,X17)|X19!=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,X19,X18)|X19!=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16))))&(~m1_subset_1(X20,u1_struct_0(X16))|(~r1_orders_2(X16,X20,X17)|~r1_orders_2(X16,X20,X18)|r1_orders_2(X16,X20,X19))|X19!=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16))))&((m1_subset_1(esk1_4(X16,X17,X18,X19),u1_struct_0(X16))|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))&(((r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X17)|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X18)|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16))))&(~r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X19)|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.21/0.40  fof(c_0_11, plain, ![X12]:(~l1_orders_2(X12)|(~v2_lattice3(X12)|~v2_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.21/0.40  cnf(c_0_12, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_13, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  fof(c_0_14, plain, ![X25]:(u1_struct_0(k2_yellow_1(X25))=X25&u1_orders_2(k2_yellow_1(X25))=k1_yellow_1(X25)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.21/0.40  fof(c_0_15, plain, ![X23]:(((v1_orders_2(k2_yellow_1(X23))&v3_orders_2(k2_yellow_1(X23)))&v4_orders_2(k2_yellow_1(X23)))&v5_orders_2(k2_yellow_1(X23))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.21/0.40  fof(c_0_16, plain, ![X22]:(v1_orders_2(k2_yellow_1(X22))&l1_orders_2(k2_yellow_1(X22))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.21/0.40  fof(c_0_17, plain, ![X13, X14, X15]:(~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|m1_subset_1(k11_lattice3(X13,X14,X15),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.21/0.40  fof(c_0_18, plain, ![X9, X10, X11]:((~r3_orders_2(X9,X10,X11)|r1_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_orders_2(X9,X10,X11)|r3_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.21/0.40  cnf(c_0_19, plain, (r1_orders_2(X1,X2,X3)|X2!=k11_lattice3(X1,X4,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.40  cnf(c_0_20, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_21, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_22, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_23, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  fof(c_0_24, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.21/0.40  cnf(c_0_25, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X3,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_26, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_27, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_28, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|X2!=k11_lattice3(k2_yellow_1(X1),X4,X3)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.21/0.40  cnf(c_0_29, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_22])])).
% 0.21/0.40  fof(c_0_30, negated_conjecture, (~v1_xboole_0(esk2_0)&(v2_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.21/0.40  cnf(c_0_31, plain, (r1_orders_2(X1,X2,X3)|X2!=k11_lattice3(X1,X3,X4)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_25, c_0_13])).
% 0.21/0.40  fof(c_0_32, plain, ![X26, X27, X28]:((~r3_orders_2(k2_yellow_1(X26),X27,X28)|r1_tarski(X27,X28)|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X26)))|~m1_subset_1(X27,u1_struct_0(k2_yellow_1(X26)))|v1_xboole_0(X26))&(~r1_tarski(X27,X28)|r3_orders_2(k2_yellow_1(X26),X27,X28)|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X26)))|~m1_subset_1(X27,u1_struct_0(k2_yellow_1(X26)))|v1_xboole_0(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.21/0.40  cnf(c_0_33, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_22]), c_0_27])])).
% 0.21/0.40  cnf(c_0_34, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (v2_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_36, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|X2!=k11_lattice3(k2_yellow_1(X1),X3,X4)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_21]), c_0_22])])).
% 0.21/0.40  fof(c_0_37, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.21/0.40  cnf(c_0_38, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.40  cnf(c_0_39, plain, (r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)|v2_struct_0(k2_yellow_1(X1))|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29])).
% 0.21/0.40  cnf(c_0_40, negated_conjecture, (~v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_35]), c_0_22])])).
% 0.21/0.40  cnf(c_0_41, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_29])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_43, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.40  cnf(c_0_44, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_20]), c_0_20])).
% 0.21/0.40  cnf(c_0_45, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_40])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_49, plain, (r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)|v2_struct_0(k2_yellow_1(X1))|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_41]), c_0_29])).
% 0.21/0.40  cnf(c_0_50, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.40  cnf(c_0_51, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_29])).
% 0.21/0.40  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_47, c_0_20])).
% 0.21/0.40  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_48, c_0_20])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_35]), c_0_40])).
% 0.21/0.40  cnf(c_0_55, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.21/0.40  cnf(c_0_56, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_54]), c_0_46]), c_0_29])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_53]), c_0_52])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 58
% 0.21/0.40  # Proof object clause steps            : 37
% 0.21/0.40  # Proof object formula steps           : 21
% 0.21/0.40  # Proof object conjectures             : 18
% 0.21/0.40  # Proof object clause conjectures      : 15
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 16
% 0.21/0.40  # Proof object initial formulas used   : 10
% 0.21/0.40  # Proof object generating inferences   : 16
% 0.21/0.40  # Proof object simplifying inferences  : 35
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 11
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 29
% 0.21/0.40  # Removed in clause preprocessing      : 1
% 0.21/0.40  # Initial clauses in saturation        : 28
% 0.21/0.40  # Processed clauses                    : 98
% 0.21/0.40  # ...of these trivial                  : 2
% 0.21/0.40  # ...subsumed                          : 11
% 0.21/0.40  # ...remaining for further processing  : 85
% 0.21/0.40  # Other redundant clauses eliminated   : 0
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 1
% 0.21/0.40  # Backward-rewritten                   : 2
% 0.21/0.40  # Generated clauses                    : 180
% 0.21/0.40  # ...of the previous two non-trivial   : 179
% 0.21/0.40  # Contextual simplify-reflections      : 16
% 0.21/0.40  # Paramodulations                      : 171
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 9
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
% 0.21/0.40  # Current number of processed clauses  : 82
% 0.21/0.40  #    Positive orientable unit clauses  : 9
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 4
% 0.21/0.40  #    Non-unit-clauses                  : 69
% 0.21/0.40  # Current number of unprocessed clauses: 105
% 0.21/0.40  # ...number of literals in the above   : 878
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 4
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 1469
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 325
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 26
% 0.21/0.40  # Unit Clause-clause subsumption calls : 9
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 1
% 0.21/0.40  # BW rewrite match successes           : 1
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 11100
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.038 s
% 0.21/0.40  # System time              : 0.008 s
% 0.21/0.40  # Total time               : 0.047 s
% 0.21/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
