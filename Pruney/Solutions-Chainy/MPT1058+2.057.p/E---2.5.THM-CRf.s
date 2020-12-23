%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:34 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 226 expanded)
%              Number of clauses        :   42 ( 100 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 430 expanded)
%              Number of equality atoms :   69 ( 208 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_16,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X37,X38] : k5_relat_1(k6_relat_1(X38),k6_relat_1(X37)) = k6_relat_1(k3_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | k10_relat_1(k7_relat_1(X36,X34),X35) = k3_xboole_0(X34,k10_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_24,plain,(
    ! [X32] :
      ( k1_relat_1(k6_relat_1(X32)) = X32
      & k2_relat_1(k6_relat_1(X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_25,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | k1_relat_1(k5_relat_1(X30,X31)) = k10_relat_1(X30,k1_relat_1(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_30,plain,(
    ! [X33] :
      ( v1_relat_1(k6_relat_1(X33))
      & v1_funct_1(k6_relat_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_31,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | r1_tarski(k10_relat_1(X25,X24),k1_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_33,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_36,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | k10_relat_1(X29,k2_xboole_0(X27,X28)) = k2_xboole_0(k10_relat_1(X29,X27),k10_relat_1(X29,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_39,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k10_relat_1(X26,k2_relat_1(X26)) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_40,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X9,X10,X11] :
      ( ( r1_tarski(X9,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) )
      & ( r1_tarski(X11,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) )
      & ( ~ r1_tarski(X10,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

fof(c_0_43,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(k10_relat_1(esk2_0,esk4_0),esk3_0)
    & k10_relat_1(esk2_0,esk4_0) != k10_relat_1(k7_relat_1(esk2_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_44,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_45,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_47,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_34])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X1,X2)),k6_relat_1(X3))) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3)) = k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_59,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_50]),c_0_34])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 = k2_xboole_0(X1,k10_relat_1(esk2_0,esk4_0))
    | r1_tarski(X1,esk1_3(X1,esk3_0,k10_relat_1(esk2_0,esk4_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(X1,X2)),X3) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_65,plain,
    ( k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(esk3_0,k10_relat_1(esk2_0,esk4_0)) = esk3_0
    | r1_tarski(esk3_0,esk1_3(esk3_0,esk3_0,k10_relat_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k10_relat_1(esk2_0,esk4_0) != k10_relat_1(k7_relat_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk2_0,X1)),X2) = k10_relat_1(k7_relat_1(esk2_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk2_0,esk4_0)),esk3_0) = k10_relat_1(esk2_0,esk4_0)
    | r1_tarski(esk3_0,esk1_3(esk3_0,esk3_0,k10_relat_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk2_0,esk4_0)),esk3_0) != k10_relat_1(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_3(esk3_0,esk3_0,k10_relat_1(esk2_0,esk4_0))) ),
    inference(sr,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( k2_xboole_0(esk3_0,k10_relat_1(esk2_0,esk4_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_54]),c_0_62])])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_73]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n016.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:24:49 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.41  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.22/0.41  # and selection function SelectNegativeLiterals.
% 0.22/0.41  #
% 0.22/0.41  # Preprocessing time       : 0.041 s
% 0.22/0.41  # Presaturation interreduction done
% 0.22/0.41  
% 0.22/0.41  # Proof found!
% 0.22/0.41  # SZS status Theorem
% 0.22/0.41  # SZS output start CNFRefutation
% 0.22/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.22/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.22/0.41  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.22/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.22/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.22/0.41  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.22/0.41  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.22/0.41  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.22/0.41  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.22/0.41  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.22/0.41  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.22/0.41  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.22/0.41  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.22/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.22/0.41  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.22/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.22/0.41  fof(c_0_16, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.22/0.41  fof(c_0_17, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.22/0.41  fof(c_0_18, plain, ![X37, X38]:k5_relat_1(k6_relat_1(X38),k6_relat_1(X37))=k6_relat_1(k3_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.22/0.41  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.41  fof(c_0_21, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.22/0.41  fof(c_0_22, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.22/0.41  fof(c_0_23, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|k10_relat_1(k7_relat_1(X36,X34),X35)=k3_xboole_0(X34,k10_relat_1(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.22/0.41  fof(c_0_24, plain, ![X32]:(k1_relat_1(k6_relat_1(X32))=X32&k2_relat_1(k6_relat_1(X32))=X32), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.22/0.41  cnf(c_0_25, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.41  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.22/0.41  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.41  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.41  fof(c_0_29, plain, ![X30, X31]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|k1_relat_1(k5_relat_1(X30,X31))=k10_relat_1(X30,k1_relat_1(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.22/0.41  fof(c_0_30, plain, ![X33]:(v1_relat_1(k6_relat_1(X33))&v1_funct_1(k6_relat_1(X33))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.22/0.41  fof(c_0_31, plain, ![X24, X25]:(~v1_relat_1(X25)|r1_tarski(k10_relat_1(X25,X24),k1_relat_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.22/0.41  fof(c_0_32, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.22/0.41  cnf(c_0_33, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.22/0.41  cnf(c_0_34, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.22/0.41  cnf(c_0_35, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.22/0.41  cnf(c_0_36, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.22/0.41  cnf(c_0_37, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.22/0.41  fof(c_0_38, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|k10_relat_1(X29,k2_xboole_0(X27,X28))=k2_xboole_0(k10_relat_1(X29,X27),k10_relat_1(X29,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.22/0.41  fof(c_0_39, plain, ![X26]:(~v1_relat_1(X26)|k10_relat_1(X26,k2_relat_1(X26))=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.22/0.41  fof(c_0_40, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.22/0.41  cnf(c_0_41, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.22/0.41  fof(c_0_42, plain, ![X9, X10, X11]:(((r1_tarski(X9,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11))&(r1_tarski(X11,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11)))&(~r1_tarski(X10,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.22/0.41  fof(c_0_43, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(k10_relat_1(esk2_0,esk4_0),esk3_0)&k10_relat_1(esk2_0,esk4_0)!=k10_relat_1(k7_relat_1(esk2_0,esk3_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.22/0.41  fof(c_0_44, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.22/0.41  cnf(c_0_45, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_26]), c_0_27]), c_0_28])).
% 0.22/0.41  cnf(c_0_46, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.22/0.41  cnf(c_0_47, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_34])).
% 0.22/0.41  cnf(c_0_48, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.22/0.41  cnf(c_0_49, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.22/0.41  cnf(c_0_50, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.22/0.41  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.22/0.41  cnf(c_0_52, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_34])).
% 0.22/0.41  cnf(c_0_53, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.22/0.41  cnf(c_0_54, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.22/0.41  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.22/0.41  cnf(c_0_56, plain, (k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X1,X2)),k6_relat_1(X3)))=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.22/0.42  cnf(c_0_57, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k10_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 0.22/0.42  cnf(c_0_58, plain, (k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3))=k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_37])).
% 0.22/0.42  cnf(c_0_59, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_50]), c_0_34])).
% 0.22/0.42  cnf(c_0_60, plain, (k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),X1)=X1), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.22/0.42  cnf(c_0_61, negated_conjecture, (esk3_0=k2_xboole_0(X1,k10_relat_1(esk2_0,esk4_0))|r1_tarski(X1,esk1_3(X1,esk3_0,k10_relat_1(esk2_0,esk4_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.22/0.42  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 0.22/0.42  cnf(c_0_63, plain, (k10_relat_1(k6_relat_1(k10_relat_1(X1,X2)),X3)=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.22/0.42  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.22/0.42  cnf(c_0_65, plain, (k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.22/0.42  cnf(c_0_66, negated_conjecture, (k2_xboole_0(esk3_0,k10_relat_1(esk2_0,esk4_0))=esk3_0|r1_tarski(esk3_0,esk1_3(esk3_0,esk3_0,k10_relat_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.22/0.42  cnf(c_0_67, negated_conjecture, (k10_relat_1(esk2_0,esk4_0)!=k10_relat_1(k7_relat_1(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.22/0.42  cnf(c_0_68, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk2_0,X1)),X2)=k10_relat_1(k7_relat_1(esk2_0,X2),X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.22/0.42  cnf(c_0_69, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk2_0,esk4_0)),esk3_0)=k10_relat_1(esk2_0,esk4_0)|r1_tarski(esk3_0,esk1_3(esk3_0,esk3_0,k10_relat_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.22/0.42  cnf(c_0_70, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk2_0,esk4_0)),esk3_0)!=k10_relat_1(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.22/0.42  cnf(c_0_71, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.22/0.42  cnf(c_0_72, negated_conjecture, (r1_tarski(esk3_0,esk1_3(esk3_0,esk3_0,k10_relat_1(esk2_0,esk4_0)))), inference(sr,[status(thm)],[c_0_69, c_0_70])).
% 0.22/0.42  cnf(c_0_73, negated_conjecture, (k2_xboole_0(esk3_0,k10_relat_1(esk2_0,esk4_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_54]), c_0_62])])).
% 0.22/0.42  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_73]), c_0_70]), ['proof']).
% 0.22/0.42  # SZS output end CNFRefutation
% 0.22/0.42  # Proof object total steps             : 75
% 0.22/0.42  # Proof object clause steps            : 42
% 0.22/0.42  # Proof object formula steps           : 33
% 0.22/0.42  # Proof object conjectures             : 14
% 0.22/0.42  # Proof object clause conjectures      : 11
% 0.22/0.42  # Proof object formula conjectures     : 3
% 0.22/0.42  # Proof object initial clauses used    : 20
% 0.22/0.42  # Proof object initial formulas used   : 16
% 0.22/0.42  # Proof object generating inferences   : 14
% 0.22/0.42  # Proof object simplifying inferences  : 21
% 0.22/0.42  # Training examples: 0 positive, 0 negative
% 0.22/0.42  # Parsed axioms                        : 16
% 0.22/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.42  # Initial clauses                      : 25
% 0.22/0.42  # Removed in clause preprocessing      : 4
% 0.22/0.42  # Initial clauses in saturation        : 21
% 0.22/0.42  # Processed clauses                    : 112
% 0.22/0.42  # ...of these trivial                  : 4
% 0.22/0.42  # ...subsumed                          : 10
% 0.22/0.42  # ...remaining for further processing  : 98
% 0.22/0.42  # Other redundant clauses eliminated   : 2
% 0.22/0.42  # Clauses deleted for lack of memory   : 0
% 0.22/0.42  # Backward-subsumed                    : 1
% 0.22/0.42  # Backward-rewritten                   : 9
% 0.22/0.42  # Generated clauses                    : 308
% 0.22/0.42  # ...of the previous two non-trivial   : 239
% 0.22/0.42  # Contextual simplify-reflections      : 0
% 0.22/0.42  # Paramodulations                      : 304
% 0.22/0.42  # Factorizations                       : 0
% 0.22/0.42  # Equation resolutions                 : 2
% 0.22/0.42  # Propositional unsat checks           : 0
% 0.22/0.42  #    Propositional check models        : 0
% 0.22/0.42  #    Propositional check unsatisfiable : 0
% 0.22/0.42  #    Propositional clauses             : 0
% 0.22/0.42  #    Propositional clauses after purity: 0
% 0.22/0.42  #    Propositional unsat core size     : 0
% 0.22/0.42  #    Propositional preprocessing time  : 0.000
% 0.22/0.42  #    Propositional encoding time       : 0.000
% 0.22/0.42  #    Propositional solver time         : 0.000
% 0.22/0.42  #    Success case prop preproc time    : 0.000
% 0.22/0.42  #    Success case prop encoding time   : 0.000
% 0.22/0.42  #    Success case prop solver time     : 0.000
% 0.22/0.42  # Current number of processed clauses  : 64
% 0.22/0.42  #    Positive orientable unit clauses  : 37
% 0.22/0.42  #    Positive unorientable unit clauses: 1
% 0.22/0.42  #    Negative unit clauses             : 1
% 0.22/0.42  #    Non-unit-clauses                  : 25
% 0.22/0.42  # Current number of unprocessed clauses: 162
% 0.22/0.42  # ...number of literals in the above   : 245
% 0.22/0.42  # Current number of archived formulas  : 0
% 0.22/0.42  # Current number of archived clauses   : 36
% 0.22/0.42  # Clause-clause subsumption calls (NU) : 163
% 0.22/0.42  # Rec. Clause-clause subsumption calls : 139
% 0.22/0.42  # Non-unit clause-clause subsumptions  : 10
% 0.22/0.42  # Unit Clause-clause subsumption calls : 30
% 0.22/0.42  # Rewrite failures with RHS unbound    : 0
% 0.22/0.42  # BW rewrite match attempts            : 27
% 0.22/0.42  # BW rewrite match successes           : 13
% 0.22/0.42  # Condensation attempts                : 0
% 0.22/0.42  # Condensation successes               : 0
% 0.22/0.42  # Termbank termtop insertions          : 6157
% 0.22/0.42  
% 0.22/0.42  # -------------------------------------------------
% 0.22/0.42  # User time                : 0.054 s
% 0.22/0.42  # System time              : 0.004 s
% 0.22/0.42  # Total time               : 0.058 s
% 0.22/0.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
