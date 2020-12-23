%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:49 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 480 expanded)
%              Number of clauses        :   52 ( 203 expanded)
%              Number of leaves         :   18 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 ( 923 expanded)
%              Number of equality atoms :   62 ( 474 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t9_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r2_hidden(k3_xboole_0(X2,X3),X1)
               => k11_lattice3(k2_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l19_yellow_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( r2_hidden(k3_xboole_0(X2,X3),k9_setfam_1(X1))
            & r2_hidden(k2_xboole_0(X2,X3),k9_setfam_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t17_yellow_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
            & k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t8_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r2_hidden(k2_xboole_0(X2,X3),X1)
               => k10_lattice3(k2_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

fof(fc8_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v3_lattice3(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_yellow_1)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(t12_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( v3_lattice3(X1)
       => ( v1_lattice3(X1)
          & v2_lattice3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_lattice3)).

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

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(c_0_18,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X36,X37,X38] :
      ( v1_xboole_0(X36)
      | ~ m1_subset_1(X37,u1_struct_0(k2_yellow_1(X36)))
      | ~ m1_subset_1(X38,u1_struct_0(k2_yellow_1(X36)))
      | ~ r2_hidden(k3_xboole_0(X37,X38),X36)
      | k11_lattice3(k2_yellow_1(X36),X37,X38) = k3_xboole_0(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_yellow_1])])])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(k3_xboole_0(X29,X30),k9_setfam_1(X28))
        | ~ m1_subset_1(X30,u1_struct_0(k3_yellow_1(X28)))
        | ~ m1_subset_1(X29,u1_struct_0(k3_yellow_1(X28))) )
      & ( r2_hidden(k2_xboole_0(X29,X30),k9_setfam_1(X28))
        | ~ m1_subset_1(X30,u1_struct_0(k3_yellow_1(X28)))
        | ~ m1_subset_1(X29,u1_struct_0(k3_yellow_1(X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l19_yellow_1])])])])).

fof(c_0_25,plain,(
    ! [X32] : k3_yellow_1(X32) = k2_yellow_1(k9_setfam_1(X32)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_26,plain,(
    ! [X13,X14] : k3_tarski(k2_tarski(X13,X14)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
           => ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
              & k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_yellow_1])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | k11_lattice3(k2_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X31] :
      ( u1_struct_0(k2_yellow_1(X31)) = X31
      & u1_orders_2(k2_yellow_1(X31)) = k1_yellow_1(X31) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_32,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X33,X34,X35] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))
      | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))
      | ~ r2_hidden(k2_xboole_0(X34,X35),X33)
      | k10_lattice3(k2_yellow_1(X33),X34,X35) = k2_xboole_0(X34,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_yellow_1])])])])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(esk2_0)))
    & ( k13_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0) != k2_xboole_0(esk3_0,esk4_0)
      | k12_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0) != k3_xboole_0(esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_38,plain,
    ( k11_lattice3(k2_yellow_1(X1),X2,X3) = k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_39,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X3))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_29]),c_0_30])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | k10_lattice3(k2_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k2_xboole_0(X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_44,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( k13_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0) != k2_xboole_0(esk3_0,esk4_0)
    | k12_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0) != k3_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k11_lattice3(k2_yellow_1(X1),X2,X3) = k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r2_hidden(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,k9_setfam_1(X3))
    | ~ m1_subset_1(X1,k9_setfam_1(X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_39]),c_0_39])).

cnf(c_0_48,plain,
    ( k10_lattice3(k2_yellow_1(X1),X2,X3) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_30]),c_0_30])).

cnf(c_0_49,plain,
    ( r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X3))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_34]),c_0_34]),c_0_43]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0) != k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0) != k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_34]),c_0_34]),c_0_43]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_51,plain,
    ( k11_lattice3(k2_yellow_1(k9_setfam_1(X1)),X2,X3) = k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | ~ m1_subset_1(X3,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k9_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k10_lattice3(k2_yellow_1(X1),X2,X3) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r2_hidden(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_39]),c_0_39]),c_0_40])).

cnf(c_0_53,plain,
    ( r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,k9_setfam_1(X3))
    | ~ m1_subset_1(X1,k9_setfam_1(X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_39]),c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) != k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | k11_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0) != k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),X2,X3) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | ~ m1_subset_1(X3,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k9_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(k9_setfam_1(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(k9_setfam_1(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_34])).

fof(c_0_60,plain,(
    ! [X27] :
      ( v1_orders_2(k3_yellow_1(X27))
      & v3_lattice3(k3_yellow_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[fc8_yellow_1])).

fof(c_0_61,plain,(
    ! [X26] :
      ( ~ v2_struct_0(k3_yellow_1(X26))
      & v1_orders_2(k3_yellow_1(X26))
      & v3_orders_2(k3_yellow_1(X26))
      & v4_orders_2(k3_yellow_1(X26))
      & v5_orders_2(k3_yellow_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

cnf(c_0_62,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0) != k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | k11_lattice3(k2_yellow_1(k9_setfam_1(X2)),esk3_0,esk4_0) != k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X2))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X2))
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk4_0,k9_setfam_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_0,k9_setfam_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_39])).

fof(c_0_65,plain,(
    ! [X23] :
      ( ( v1_lattice3(X23)
        | ~ v3_lattice3(X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( v2_lattice3(X23)
        | ~ v3_lattice3(X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_lattice3])])])])).

cnf(c_0_66,plain,
    ( v3_lattice3(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_67,plain,(
    ! [X24] :
      ( v1_orders_2(k2_yellow_1(X24))
      & l1_orders_2(k2_yellow_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

cnf(c_0_68,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0) != k11_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0) != k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

fof(c_0_70,plain,(
    ! [X17,X18,X19] :
      ( ~ v5_orders_2(X17)
      | ~ v2_lattice3(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k12_lattice3(X17,X18,X19) = k11_lattice3(X17,X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_71,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( v3_lattice3(k2_yellow_1(k9_setfam_1(X1))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_34])).

cnf(c_0_73,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( ~ v2_struct_0(k2_yellow_1(k9_setfam_1(X1))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_34])).

fof(c_0_75,plain,(
    ! [X25] :
      ( v1_orders_2(k2_yellow_1(X25))
      & v3_orders_2(k2_yellow_1(X25))
      & v4_orders_2(k2_yellow_1(X25))
      & v5_orders_2(k2_yellow_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

cnf(c_0_76,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0) != k11_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) != k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_57])).

cnf(c_0_77,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,plain,
    ( v2_lattice3(k2_yellow_1(k9_setfam_1(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])]),c_0_74])).

cnf(c_0_79,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) != k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_39]),c_0_63]),c_0_39]),c_0_64]),c_0_73]),c_0_78]),c_0_79])])).

cnf(c_0_81,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0) != k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X2))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X2))
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_57])).

fof(c_0_82,plain,(
    ! [X20,X21,X22] :
      ( ~ v5_orders_2(X20)
      | ~ v1_lattice3(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | k13_lattice3(X20,X21,X22) = k10_lattice3(X20,X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_83,plain,
    ( v1_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_84,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0) != k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_63]),c_0_64])])).

cnf(c_0_85,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_86,plain,
    ( v1_lattice3(k2_yellow_1(k9_setfam_1(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_72]),c_0_73])]),c_0_74])).

cnf(c_0_87,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0) != k10_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k9_setfam_1(X1))
    | ~ m1_subset_1(esk3_0,k9_setfam_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_39]),c_0_63]),c_0_39]),c_0_64]),c_0_73]),c_0_79])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_87]),c_0_63]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.36  fof(t9_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r2_hidden(k3_xboole_0(X2,X3),X1)=>k11_lattice3(k2_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_1)).
% 0.12/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.36  fof(l19_yellow_1, axiom, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(r2_hidden(k3_xboole_0(X2,X3),k9_setfam_1(X1))&r2_hidden(k2_xboole_0(X2,X3),k9_setfam_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l19_yellow_1)).
% 0.12/0.36  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.12/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.36  fof(t17_yellow_1, conjecture, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(k13_lattice3(k3_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3)&k12_lattice3(k3_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow_1)).
% 0.12/0.36  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.12/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.36  fof(t8_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r2_hidden(k2_xboole_0(X2,X3),X1)=>k10_lattice3(k2_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_1)).
% 0.12/0.36  fof(fc8_yellow_1, axiom, ![X1]:(v1_orders_2(k3_yellow_1(X1))&v3_lattice3(k3_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_yellow_1)).
% 0.12/0.36  fof(fc7_yellow_1, axiom, ![X1]:((((~(v2_struct_0(k3_yellow_1(X1)))&v1_orders_2(k3_yellow_1(X1)))&v3_orders_2(k3_yellow_1(X1)))&v4_orders_2(k3_yellow_1(X1)))&v5_orders_2(k3_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_yellow_1)).
% 0.12/0.37  fof(t12_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>(v3_lattice3(X1)=>(v1_lattice3(X1)&v2_lattice3(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_lattice3)).
% 0.12/0.37  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.12/0.37  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.12/0.37  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.12/0.37  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.12/0.37  fof(c_0_18, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.37  fof(c_0_19, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_20, plain, ![X36, X37, X38]:(v1_xboole_0(X36)|(~m1_subset_1(X37,u1_struct_0(k2_yellow_1(X36)))|(~m1_subset_1(X38,u1_struct_0(k2_yellow_1(X36)))|(~r2_hidden(k3_xboole_0(X37,X38),X36)|k11_lattice3(k2_yellow_1(X36),X37,X38)=k3_xboole_0(X37,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_yellow_1])])])])).
% 0.12/0.37  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  fof(c_0_23, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_24, plain, ![X28, X29, X30]:((r2_hidden(k3_xboole_0(X29,X30),k9_setfam_1(X28))|~m1_subset_1(X30,u1_struct_0(k3_yellow_1(X28)))|~m1_subset_1(X29,u1_struct_0(k3_yellow_1(X28))))&(r2_hidden(k2_xboole_0(X29,X30),k9_setfam_1(X28))|~m1_subset_1(X30,u1_struct_0(k3_yellow_1(X28)))|~m1_subset_1(X29,u1_struct_0(k3_yellow_1(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l19_yellow_1])])])])).
% 0.12/0.37  fof(c_0_25, plain, ![X32]:k3_yellow_1(X32)=k2_yellow_1(k9_setfam_1(X32)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.12/0.37  fof(c_0_26, plain, ![X13, X14]:k3_tarski(k2_tarski(X13,X14))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.37  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(k13_lattice3(k3_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3)&k12_lattice3(k3_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t17_yellow_1])).
% 0.12/0.37  cnf(c_0_28, plain, (v1_xboole_0(X1)|k11_lattice3(k2_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~r2_hidden(k3_xboole_0(X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  fof(c_0_31, plain, ![X31]:(u1_struct_0(k2_yellow_1(X31))=X31&u1_orders_2(k2_yellow_1(X31))=k1_yellow_1(X31)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.12/0.37  fof(c_0_32, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.37  cnf(c_0_33, plain, (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_34, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  fof(c_0_35, plain, ![X33, X34, X35]:(v1_xboole_0(X33)|(~m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))|(~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))|(~r2_hidden(k2_xboole_0(X34,X35),X33)|k10_lattice3(k2_yellow_1(X33),X34,X35)=k2_xboole_0(X34,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_yellow_1])])])])).
% 0.12/0.37  cnf(c_0_36, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  fof(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(esk2_0)))&(k13_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0)!=k2_xboole_0(esk3_0,esk4_0)|k12_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0)!=k3_xboole_0(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.12/0.37  cnf(c_0_38, plain, (k11_lattice3(k2_yellow_1(X1),X2,X3)=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|v1_xboole_0(X1)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))|~r2_hidden(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 0.12/0.37  cnf(c_0_39, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_41, plain, (r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X3))))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_29]), c_0_30])).
% 0.12/0.37  cnf(c_0_42, plain, (v1_xboole_0(X1)|k10_lattice3(k2_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~r2_hidden(k2_xboole_0(X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_43, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 0.12/0.37  cnf(c_0_44, plain, (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (k13_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0)!=k2_xboole_0(esk3_0,esk4_0)|k12_lattice3(k3_yellow_1(esk2_0),esk3_0,esk4_0)!=k3_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_46, plain, (k11_lattice3(k2_yellow_1(X1),X2,X3)=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r2_hidden(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_40])).
% 0.12/0.37  cnf(c_0_47, plain, (r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))|~m1_subset_1(X2,k9_setfam_1(X3))|~m1_subset_1(X1,k9_setfam_1(X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_39]), c_0_39])).
% 0.12/0.37  cnf(c_0_48, plain, (k10_lattice3(k2_yellow_1(X1),X2,X3)=k3_tarski(k2_enumset1(X2,X2,X2,X3))|v1_xboole_0(X1)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))|~r2_hidden(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_30]), c_0_30])).
% 0.12/0.37  cnf(c_0_49, plain, (r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X3))))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_34]), c_0_34]), c_0_43]), c_0_30])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)!=k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)!=k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_34]), c_0_34]), c_0_43]), c_0_29]), c_0_30]), c_0_30])).
% 0.12/0.37  cnf(c_0_51, plain, (k11_lattice3(k2_yellow_1(k9_setfam_1(X1)),X2,X3)=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|~m1_subset_1(X3,k9_setfam_1(X1))|~m1_subset_1(X2,k9_setfam_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.37  cnf(c_0_52, plain, (k10_lattice3(k2_yellow_1(X1),X2,X3)=k3_tarski(k2_enumset1(X2,X2,X2,X3))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r2_hidden(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_39]), c_0_39]), c_0_40])).
% 0.12/0.37  cnf(c_0_53, plain, (r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X3))|~m1_subset_1(X2,k9_setfam_1(X3))|~m1_subset_1(X1,k9_setfam_1(X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_39]), c_0_39])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))!=k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|k11_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0)!=k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.37  cnf(c_0_57, plain, (k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),X2,X3)=k3_tarski(k2_enumset1(X2,X2,X2,X3))|~m1_subset_1(X3,k9_setfam_1(X1))|~m1_subset_1(X2,k9_setfam_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(k9_setfam_1(esk2_0))))), inference(rw,[status(thm)],[c_0_54, c_0_34])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(k9_setfam_1(esk2_0))))), inference(rw,[status(thm)],[c_0_55, c_0_34])).
% 0.12/0.37  fof(c_0_60, plain, ![X27]:(v1_orders_2(k3_yellow_1(X27))&v3_lattice3(k3_yellow_1(X27))), inference(variable_rename,[status(thm)],[fc8_yellow_1])).
% 0.12/0.37  fof(c_0_61, plain, ![X26]:((((~v2_struct_0(k3_yellow_1(X26))&v1_orders_2(k3_yellow_1(X26)))&v3_orders_2(k3_yellow_1(X26)))&v4_orders_2(k3_yellow_1(X26)))&v5_orders_2(k3_yellow_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0)!=k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|k11_lattice3(k2_yellow_1(k9_setfam_1(X2)),esk3_0,esk4_0)!=k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X2))|~m1_subset_1(esk3_0,k9_setfam_1(X2))|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk4_0,k9_setfam_1(esk2_0))), inference(rw,[status(thm)],[c_0_58, c_0_39])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk3_0,k9_setfam_1(esk2_0))), inference(rw,[status(thm)],[c_0_59, c_0_39])).
% 0.12/0.37  fof(c_0_65, plain, ![X23]:((v1_lattice3(X23)|~v3_lattice3(X23)|(v2_struct_0(X23)|~l1_orders_2(X23)))&(v2_lattice3(X23)|~v3_lattice3(X23)|(v2_struct_0(X23)|~l1_orders_2(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_lattice3])])])])).
% 0.12/0.37  cnf(c_0_66, plain, (v3_lattice3(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.37  fof(c_0_67, plain, ![X24]:(v1_orders_2(k2_yellow_1(X24))&l1_orders_2(k2_yellow_1(X24))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.12/0.37  cnf(c_0_68, plain, (~v2_struct_0(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)!=k11_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0)!=k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.12/0.37  fof(c_0_70, plain, ![X17, X18, X19]:(~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|k12_lattice3(X17,X18,X19)=k11_lattice3(X17,X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.12/0.37  cnf(c_0_71, plain, (v2_lattice3(X1)|v2_struct_0(X1)|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.37  cnf(c_0_72, plain, (v3_lattice3(k2_yellow_1(k9_setfam_1(X1)))), inference(rw,[status(thm)],[c_0_66, c_0_34])).
% 0.12/0.37  cnf(c_0_73, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.12/0.37  cnf(c_0_74, plain, (~v2_struct_0(k2_yellow_1(k9_setfam_1(X1)))), inference(rw,[status(thm)],[c_0_68, c_0_34])).
% 0.12/0.37  fof(c_0_75, plain, ![X25]:(((v1_orders_2(k2_yellow_1(X25))&v3_orders_2(k2_yellow_1(X25)))&v4_orders_2(k2_yellow_1(X25)))&v5_orders_2(k2_yellow_1(X25))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, (k12_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)!=k11_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))!=k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_57])).
% 0.12/0.37  cnf(c_0_77, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.12/0.37  cnf(c_0_78, plain, (v2_lattice3(k2_yellow_1(k9_setfam_1(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])]), c_0_74])).
% 0.12/0.37  cnf(c_0_79, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.12/0.37  cnf(c_0_80, negated_conjecture, (k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))!=k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_39]), c_0_63]), c_0_39]), c_0_64]), c_0_73]), c_0_78]), c_0_79])])).
% 0.12/0.37  cnf(c_0_81, negated_conjecture, (k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0)!=k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X2))|~m1_subset_1(esk3_0,k9_setfam_1(X2))|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_57])).
% 0.12/0.37  fof(c_0_82, plain, ![X20, X21, X22]:(~v5_orders_2(X20)|~v1_lattice3(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))|k13_lattice3(X20,X21,X22)=k10_lattice3(X20,X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.12/0.37  cnf(c_0_83, plain, (v1_lattice3(X1)|v2_struct_0(X1)|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.37  cnf(c_0_84, negated_conjecture, (k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0)!=k13_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_63]), c_0_64])])).
% 0.12/0.37  cnf(c_0_85, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.12/0.37  cnf(c_0_86, plain, (v1_lattice3(k2_yellow_1(k9_setfam_1(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_72]), c_0_73])]), c_0_74])).
% 0.12/0.37  cnf(c_0_87, negated_conjecture, (k10_lattice3(k2_yellow_1(k9_setfam_1(X1)),esk3_0,esk4_0)!=k10_lattice3(k2_yellow_1(k9_setfam_1(esk2_0)),esk3_0,esk4_0)|~m1_subset_1(esk4_0,k9_setfam_1(X1))|~m1_subset_1(esk3_0,k9_setfam_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_39]), c_0_63]), c_0_39]), c_0_64]), c_0_73]), c_0_79])])).
% 0.12/0.37  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_87]), c_0_63]), c_0_64])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 89
% 0.12/0.37  # Proof object clause steps            : 52
% 0.12/0.37  # Proof object formula steps           : 37
% 0.12/0.37  # Proof object conjectures             : 20
% 0.12/0.37  # Proof object clause conjectures      : 17
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 22
% 0.12/0.37  # Proof object initial formulas used   : 18
% 0.12/0.37  # Proof object generating inferences   : 13
% 0.12/0.37  # Proof object simplifying inferences  : 69
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 18
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 33
% 0.12/0.37  # Removed in clause preprocessing      : 6
% 0.12/0.37  # Initial clauses in saturation        : 27
% 0.12/0.37  # Processed clauses                    : 70
% 0.12/0.37  # ...of these trivial                  : 6
% 0.12/0.37  # ...subsumed                          : 5
% 0.12/0.37  # ...remaining for further processing  : 59
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 5
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 33
% 0.12/0.37  # ...of the previous two non-trivial   : 30
% 0.12/0.37  # Contextual simplify-reflections      : 2
% 0.12/0.37  # Paramodulations                      : 32
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 33
% 0.12/0.37  #    Positive orientable unit clauses  : 11
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 21
% 0.12/0.37  # Current number of unprocessed clauses: 8
% 0.12/0.37  # ...number of literals in the above   : 41
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 32
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 267
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 31
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3551
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.031 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
