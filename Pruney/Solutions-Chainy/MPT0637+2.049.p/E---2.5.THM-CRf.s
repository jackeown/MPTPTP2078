%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:31 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   91 (1542 expanded)
%              Number of clauses        :   56 ( 663 expanded)
%              Number of leaves         :   17 ( 439 expanded)
%              Depth                    :   18
%              Number of atoms          :  179 (3030 expanded)
%              Number of equality atoms :   69 (1063 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_17,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k5_relat_1(X30,k6_relat_1(k2_relat_1(X30))) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_18,plain,(
    ! [X23] :
      ( k1_relat_1(k6_relat_1(X23)) = X23
      & k2_relat_1(k6_relat_1(X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_19,plain,(
    ! [X35] :
      ( v1_relat_1(k6_relat_1(X35))
      & v1_funct_1(k6_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k7_relat_1(k5_relat_1(X18,X19),X17) = k5_relat_1(k7_relat_1(X18,X17),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_22,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | k7_relat_1(X34,X33) = k5_relat_1(k6_relat_1(X33),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | v1_relat_1(k5_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_27,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(k1_relat_1(X27),X26)
      | k5_relat_1(k6_relat_1(X26),X27) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X13,X14] : k1_setfam_1(k2_tarski(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_34,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_35,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24])])).

cnf(c_0_38,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),X3) = k5_relat_1(k6_relat_1(X2),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_32])).

fof(c_0_39,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_43,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | k1_relat_1(k7_relat_1(X32,X31)) = k3_xboole_0(k1_relat_1(X32),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_44,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30]),c_0_24])])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(X2))),X2) = k7_relat_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_44]),c_0_24])]),c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_52,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_47]),c_0_48])).

cnf(c_0_53,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(k1_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_50])).

fof(c_0_54,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(k5_relat_1(X25,k6_relat_1(X24)),X25)
        | ~ v1_relat_1(X25) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X24),X25),X25)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_55,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k5_relat_1(k5_relat_1(X20,X21),X22) = k5_relat_1(X20,k5_relat_1(X21,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_32]),c_0_24]),c_0_24])])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),k7_relat_1(X1,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_56]),c_0_57])).

cnf(c_0_61,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_24])]),c_0_32])).

cnf(c_0_63,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_45]),c_0_61]),c_0_24])])).

fof(c_0_64,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(k2_relat_1(X29),X28)
      | k5_relat_1(X29,k6_relat_1(X28)) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_24]),c_0_24])])).

cnf(c_0_67,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_31])).

cnf(c_0_69,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_66])])).

cnf(c_0_70,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_61]),c_0_24])]),c_0_45])).

cnf(c_0_71,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_23]),c_0_24])])).

fof(c_0_72,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_61]),c_0_24])])).

cnf(c_0_74,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(X2)))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_70])).

cnf(c_0_75,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_71]),c_0_24]),c_0_24])]),c_0_45]),c_0_45])).

fof(c_0_76,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_71])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_61]),c_0_45]),c_0_24])])).

cnf(c_0_80,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3)) = k5_relat_1(k6_relat_1(X1),X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_71]),c_0_24]),c_0_24])])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_31])).

cnf(c_0_83,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_31])).

cnf(c_0_84,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_47]),c_0_48])).

cnf(c_0_86,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X2) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_87,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_36]),c_0_69])).

cnf(c_0_88,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_85,c_0_70])).

cnf(c_0_89,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_86]),c_0_87]),c_0_24])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:31:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.52/1.73  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.52/1.73  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.52/1.73  #
% 1.52/1.73  # Preprocessing time       : 0.027 s
% 1.52/1.73  # Presaturation interreduction done
% 1.52/1.73  
% 1.52/1.73  # Proof found!
% 1.52/1.73  # SZS status Theorem
% 1.52/1.73  # SZS output start CNFRefutation
% 1.52/1.73  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 1.52/1.73  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.52/1.73  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.52/1.73  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.52/1.73  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 1.52/1.73  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.52/1.73  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 1.52/1.73  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.52/1.73  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.52/1.73  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.52/1.73  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.52/1.73  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.52/1.73  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.52/1.73  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 1.52/1.73  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 1.52/1.73  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.52/1.73  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.52/1.73  fof(c_0_17, plain, ![X30]:(~v1_relat_1(X30)|k5_relat_1(X30,k6_relat_1(k2_relat_1(X30)))=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 1.52/1.73  fof(c_0_18, plain, ![X23]:(k1_relat_1(k6_relat_1(X23))=X23&k2_relat_1(k6_relat_1(X23))=X23), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.52/1.73  fof(c_0_19, plain, ![X35]:(v1_relat_1(k6_relat_1(X35))&v1_funct_1(k6_relat_1(X35))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 1.52/1.73  fof(c_0_20, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.52/1.73  fof(c_0_21, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k7_relat_1(k5_relat_1(X18,X19),X17)=k5_relat_1(k7_relat_1(X18,X17),X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 1.52/1.73  cnf(c_0_22, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.52/1.73  cnf(c_0_23, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.52/1.73  cnf(c_0_24, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.52/1.73  fof(c_0_25, plain, ![X33, X34]:(~v1_relat_1(X34)|k7_relat_1(X34,X33)=k5_relat_1(k6_relat_1(X33),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 1.52/1.73  fof(c_0_26, plain, ![X15, X16]:(~v1_relat_1(X15)|~v1_relat_1(X16)|v1_relat_1(k5_relat_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 1.52/1.73  fof(c_0_27, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(k1_relat_1(X27),X26)|k5_relat_1(k6_relat_1(X26),X27)=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 1.52/1.73  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.52/1.73  cnf(c_0_29, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.52/1.73  cnf(c_0_30, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 1.52/1.73  cnf(c_0_31, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.52/1.73  cnf(c_0_32, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.52/1.73  fof(c_0_33, plain, ![X13, X14]:k1_setfam_1(k2_tarski(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.52/1.73  fof(c_0_34, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.52/1.73  cnf(c_0_35, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.52/1.73  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 1.52/1.73  cnf(c_0_37, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24])])).
% 1.52/1.73  cnf(c_0_38, plain, (k5_relat_1(k7_relat_1(X1,X2),X3)=k5_relat_1(k6_relat_1(X2),k5_relat_1(X1,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_32])).
% 1.52/1.73  fof(c_0_39, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.52/1.73  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.52/1.73  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.52/1.73  fof(c_0_42, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.52/1.73  fof(c_0_43, plain, ![X31, X32]:(~v1_relat_1(X32)|k1_relat_1(k7_relat_1(X32,X31))=k3_xboole_0(k1_relat_1(X32),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 1.52/1.73  cnf(c_0_44, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.52/1.73  cnf(c_0_45, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_30]), c_0_24])])).
% 1.52/1.73  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.52/1.73  cnf(c_0_47, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 1.52/1.73  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.52/1.73  cnf(c_0_49, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.52/1.73  cnf(c_0_50, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(X2))),X2)=k7_relat_1(X2,X1)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_44]), c_0_24])]), c_0_45])).
% 1.52/1.73  cnf(c_0_51, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 1.52/1.73  cnf(c_0_52, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_47]), c_0_48])).
% 1.52/1.73  cnf(c_0_53, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(k1_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_50])).
% 1.52/1.73  fof(c_0_54, plain, ![X24, X25]:((r1_tarski(k5_relat_1(X25,k6_relat_1(X24)),X25)|~v1_relat_1(X25))&(r1_tarski(k5_relat_1(k6_relat_1(X24),X25),X25)|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 1.52/1.73  fof(c_0_55, plain, ![X20, X21, X22]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~v1_relat_1(X22)|k5_relat_1(k5_relat_1(X20,X21),X22)=k5_relat_1(X20,k5_relat_1(X21,X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 1.52/1.73  cnf(c_0_56, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.52/1.73  cnf(c_0_57, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_32]), c_0_24]), c_0_24])])).
% 1.52/1.73  cnf(c_0_58, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.52/1.73  cnf(c_0_59, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.52/1.73  cnf(c_0_60, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),k7_relat_1(X1,X2))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_56]), c_0_57])).
% 1.52/1.73  cnf(c_0_61, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.52/1.73  cnf(c_0_62, plain, (r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_24])]), c_0_32])).
% 1.52/1.73  cnf(c_0_63, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_45]), c_0_61]), c_0_24])])).
% 1.52/1.73  fof(c_0_64, plain, ![X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(k2_relat_1(X29),X28)|k5_relat_1(X29,k6_relat_1(X28))=X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 1.52/1.73  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.52/1.73  cnf(c_0_66, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_24]), c_0_24])])).
% 1.52/1.73  cnf(c_0_67, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.52/1.73  cnf(c_0_68, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_56, c_0_31])).
% 1.52/1.73  cnf(c_0_69, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_66])])).
% 1.52/1.73  cnf(c_0_70, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_61]), c_0_24])]), c_0_45])).
% 1.52/1.73  cnf(c_0_71, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_23]), c_0_24])])).
% 1.52/1.73  fof(c_0_72, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 1.52/1.73  cnf(c_0_73, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_61]), c_0_24])])).
% 1.52/1.73  cnf(c_0_74, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(X2))))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_52, c_0_70])).
% 1.52/1.73  cnf(c_0_75, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_71]), c_0_24]), c_0_24])]), c_0_45]), c_0_45])).
% 1.52/1.73  fof(c_0_76, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).
% 1.52/1.73  cnf(c_0_77, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 1.52/1.73  cnf(c_0_78, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_75, c_0_71])).
% 1.52/1.73  cnf(c_0_79, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_61]), c_0_45]), c_0_24])])).
% 1.52/1.73  cnf(c_0_80, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.52/1.73  cnf(c_0_81, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))=k5_relat_1(k6_relat_1(X1),X3)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_71]), c_0_24]), c_0_24])])).
% 1.52/1.73  cnf(c_0_82, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_77, c_0_31])).
% 1.52/1.73  cnf(c_0_83, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_57, c_0_31])).
% 1.52/1.73  cnf(c_0_84, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.52/1.73  cnf(c_0_85, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_47]), c_0_48])).
% 1.52/1.73  cnf(c_0_86, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X2)=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_81]), c_0_82]), c_0_83])).
% 1.52/1.73  cnf(c_0_87, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))))=k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_36]), c_0_69])).
% 1.52/1.73  cnf(c_0_88, negated_conjecture, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_85, c_0_70])).
% 1.52/1.73  cnf(c_0_89, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_86]), c_0_87]), c_0_24])])).
% 1.52/1.73  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89])]), ['proof']).
% 1.52/1.73  # SZS output end CNFRefutation
% 1.52/1.73  # Proof object total steps             : 91
% 1.52/1.73  # Proof object clause steps            : 56
% 1.52/1.73  # Proof object formula steps           : 35
% 1.52/1.73  # Proof object conjectures             : 7
% 1.52/1.73  # Proof object clause conjectures      : 4
% 1.52/1.73  # Proof object formula conjectures     : 3
% 1.52/1.73  # Proof object initial clauses used    : 19
% 1.52/1.73  # Proof object initial formulas used   : 17
% 1.52/1.73  # Proof object generating inferences   : 29
% 1.52/1.73  # Proof object simplifying inferences  : 63
% 1.52/1.73  # Training examples: 0 positive, 0 negative
% 1.52/1.73  # Parsed axioms                        : 17
% 1.52/1.73  # Removed by relevancy pruning/SinE    : 0
% 1.52/1.73  # Initial clauses                      : 22
% 1.52/1.73  # Removed in clause preprocessing      : 3
% 1.52/1.73  # Initial clauses in saturation        : 19
% 1.52/1.73  # Processed clauses                    : 4902
% 1.52/1.73  # ...of these trivial                  : 109
% 1.52/1.73  # ...subsumed                          : 3957
% 1.52/1.73  # ...remaining for further processing  : 836
% 1.52/1.73  # Other redundant clauses eliminated   : 2
% 1.52/1.73  # Clauses deleted for lack of memory   : 0
% 1.52/1.73  # Backward-subsumed                    : 33
% 1.52/1.73  # Backward-rewritten                   : 53
% 1.52/1.73  # Generated clauses                    : 134686
% 1.52/1.73  # ...of the previous two non-trivial   : 119132
% 1.52/1.73  # Contextual simplify-reflections      : 161
% 1.52/1.73  # Paramodulations                      : 134684
% 1.52/1.73  # Factorizations                       : 0
% 1.52/1.73  # Equation resolutions                 : 2
% 1.52/1.73  # Propositional unsat checks           : 0
% 1.52/1.73  #    Propositional check models        : 0
% 1.52/1.73  #    Propositional check unsatisfiable : 0
% 1.52/1.73  #    Propositional clauses             : 0
% 1.52/1.73  #    Propositional clauses after purity: 0
% 1.52/1.73  #    Propositional unsat core size     : 0
% 1.52/1.73  #    Propositional preprocessing time  : 0.000
% 1.52/1.73  #    Propositional encoding time       : 0.000
% 1.52/1.73  #    Propositional solver time         : 0.000
% 1.52/1.73  #    Success case prop preproc time    : 0.000
% 1.52/1.73  #    Success case prop encoding time   : 0.000
% 1.52/1.73  #    Success case prop solver time     : 0.000
% 1.52/1.73  # Current number of processed clauses  : 730
% 1.52/1.73  #    Positive orientable unit clauses  : 49
% 1.52/1.73  #    Positive unorientable unit clauses: 1
% 1.52/1.73  #    Negative unit clauses             : 2
% 1.52/1.73  #    Non-unit-clauses                  : 678
% 1.52/1.73  # Current number of unprocessed clauses: 114172
% 1.52/1.73  # ...number of literals in the above   : 446431
% 1.52/1.73  # Current number of archived formulas  : 0
% 1.52/1.73  # Current number of archived clauses   : 107
% 1.52/1.73  # Clause-clause subsumption calls (NU) : 69683
% 1.52/1.73  # Rec. Clause-clause subsumption calls : 58194
% 1.52/1.73  # Non-unit clause-clause subsumptions  : 4092
% 1.52/1.73  # Unit Clause-clause subsumption calls : 80
% 1.52/1.73  # Rewrite failures with RHS unbound    : 0
% 1.52/1.73  # BW rewrite match attempts            : 282
% 1.52/1.73  # BW rewrite match successes           : 83
% 1.52/1.73  # Condensation attempts                : 0
% 1.52/1.73  # Condensation successes               : 0
% 1.52/1.73  # Termbank termtop insertions          : 3179978
% 1.52/1.74  
% 1.52/1.74  # -------------------------------------------------
% 1.52/1.74  # User time                : 1.343 s
% 1.52/1.74  # System time              : 0.050 s
% 1.52/1.74  # Total time               : 1.394 s
% 1.52/1.74  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
