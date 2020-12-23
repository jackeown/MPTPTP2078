%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:33 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  111 (1157 expanded)
%              Number of clauses        :   68 ( 503 expanded)
%              Number of leaves         :   21 ( 325 expanded)
%              Depth                    :   20
%              Number of atoms          :  199 (1665 expanded)
%              Number of equality atoms :   83 (1050 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(c_0_21,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_37,plain,(
    ! [X46,X47] : k5_relat_1(k6_relat_1(X47),k6_relat_1(X46)) = k6_relat_1(k3_xboole_0(X46,X47)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X32] :
      ( k1_relat_1(k6_relat_1(X32)) = X32
      & k2_relat_1(k6_relat_1(X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_42,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))))) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_28]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_45,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_28]),c_0_34]),c_0_35])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_49,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | k7_relat_1(X34,X33) = k5_relat_1(k6_relat_1(X33),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_50,plain,(
    ! [X35] :
      ( v1_relat_1(k6_relat_1(X35))
      & v1_funct_1(k6_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_55,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k2_relat_1(k7_relat_1(X28,X27)) = k9_relat_1(X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_56,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_57,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_59,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(k6_relat_1(X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_54])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

fof(c_0_64,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | k9_relat_1(X42,k10_relat_1(X42,X41)) = k3_xboole_0(X41,k9_relat_1(X42,k1_relat_1(X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

fof(c_0_65,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | k10_relat_1(X31,k2_relat_1(X31)) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_66,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X38)
      | k10_relat_1(k7_relat_1(X38,X36),X37) = k3_xboole_0(X36,k10_relat_1(X38,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_67,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | r1_tarski(k10_relat_1(X30,X29),k1_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_68,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | ~ r1_tarski(X43,k1_relat_1(X45))
      | ~ r1_tarski(k9_relat_1(X45,X43),X44)
      | r1_tarski(X43,k10_relat_1(X45,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_61])).

cnf(c_0_70,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_72,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ r1_tarski(X39,k2_relat_1(X40))
      | k9_relat_1(X40,k10_relat_1(X40,X39)) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_73,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_75,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_77,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_81,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_28]),c_0_34]),c_0_35])).

cnf(c_0_82,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_45]),c_0_74]),c_0_54])])).

cnf(c_0_84,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_28]),c_0_34]),c_0_35])).

cnf(c_0_85,plain,
    ( k1_relat_1(X1) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0))
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_54]),c_0_74])])).

cnf(c_0_87,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),k6_relat_1(X2))) = k9_relat_1(X1,k10_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_81,c_0_48])).

cnf(c_0_88,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_80]),c_0_54]),c_0_45]),c_0_63])])).

cnf(c_0_89,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_48])).

cnf(c_0_90,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X1,X2)),k6_relat_1(X3))) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_48])).

cnf(c_0_91,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k10_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_74]),c_0_54]),c_0_74]),c_0_63])])).

cnf(c_0_92,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_74]),c_0_88]),c_0_80]),c_0_54])])).

cnf(c_0_93,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_53]),c_0_54])])).

cnf(c_0_94,negated_conjecture,
    ( k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1)) = k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_54])]),c_0_92])).

cnf(c_0_95,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_59]),c_0_54])])).

cnf(c_0_96,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_97,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0),esk2_0) = k10_relat_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_91]),c_0_88])).

cnf(c_0_98,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_95])).

cnf(c_0_99,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_53]),c_0_54])])).

cnf(c_0_100,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_83]),c_0_54])])).

cnf(c_0_101,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k10_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_97]),c_0_98]),c_0_99]),c_0_98]),c_0_70])])).

cnf(c_0_103,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_53]),c_0_101]),c_0_54])])).

cnf(c_0_104,negated_conjecture,
    ( k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k6_relat_1(k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_102])).

cnf(c_0_105,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[c_0_100,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0)) = k10_relat_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_83])).

cnf(c_0_107,plain,
    ( k9_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3)) = k10_relat_1(k7_relat_1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_90,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_109,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])]),c_0_109]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:50:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.76  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.53/0.76  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.53/0.76  #
% 0.53/0.76  # Preprocessing time       : 0.029 s
% 0.53/0.76  # Presaturation interreduction done
% 0.53/0.76  
% 0.53/0.76  # Proof found!
% 0.53/0.76  # SZS status Theorem
% 0.53/0.76  # SZS output start CNFRefutation
% 0.53/0.76  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.53/0.76  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.53/0.76  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.53/0.76  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.53/0.76  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.53/0.76  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.53/0.76  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.53/0.76  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.53/0.76  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.53/0.76  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.53/0.76  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.53/0.76  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.53/0.76  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.53/0.76  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.53/0.76  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.53/0.76  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.53/0.76  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.53/0.76  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.53/0.76  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.53/0.76  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.53/0.76  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.53/0.76  fof(c_0_21, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.53/0.76  fof(c_0_22, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.53/0.76  fof(c_0_23, plain, ![X7, X8]:k4_xboole_0(X7,X8)=k5_xboole_0(X7,k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.53/0.76  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.76  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.76  fof(c_0_26, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.53/0.76  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.76  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.53/0.76  fof(c_0_29, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.53/0.76  fof(c_0_30, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.53/0.76  fof(c_0_31, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X10,X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.53/0.76  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.53/0.76  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.53/0.76  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.76  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.76  fof(c_0_36, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.53/0.76  fof(c_0_37, plain, ![X46, X47]:k5_relat_1(k6_relat_1(X47),k6_relat_1(X46))=k6_relat_1(k3_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.53/0.76  cnf(c_0_38, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.76  cnf(c_0_39, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])).
% 0.53/0.76  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.53/0.76  fof(c_0_41, plain, ![X32]:(k1_relat_1(k6_relat_1(X32))=X32&k2_relat_1(k6_relat_1(X32))=X32), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.53/0.76  cnf(c_0_42, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.53/0.76  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.53/0.76  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))))))=k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_28]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35])).
% 0.53/0.76  cnf(c_0_45, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.53/0.76  cnf(c_0_46, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_28]), c_0_34]), c_0_35])).
% 0.53/0.76  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.53/0.76  cnf(c_0_48, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.53/0.76  fof(c_0_49, plain, ![X33, X34]:(~v1_relat_1(X34)|k7_relat_1(X34,X33)=k5_relat_1(k6_relat_1(X33),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.53/0.76  fof(c_0_50, plain, ![X35]:(v1_relat_1(k6_relat_1(X35))&v1_funct_1(k6_relat_1(X35))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.53/0.76  fof(c_0_51, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.53/0.76  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.53/0.76  cnf(c_0_53, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.53/0.76  cnf(c_0_54, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.53/0.76  fof(c_0_55, plain, ![X27, X28]:(~v1_relat_1(X28)|k2_relat_1(k7_relat_1(X28,X27))=k9_relat_1(X28,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.53/0.76  fof(c_0_56, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.53/0.76  fof(c_0_57, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.53/0.76  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.53/0.76  cnf(c_0_59, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.53/0.76  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.53/0.76  cnf(c_0_61, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.53/0.76  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(k6_relat_1(X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_54])])).
% 0.53/0.76  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.53/0.76  fof(c_0_64, plain, ![X41, X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|k9_relat_1(X42,k10_relat_1(X42,X41))=k3_xboole_0(X41,k9_relat_1(X42,k1_relat_1(X42)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.53/0.76  fof(c_0_65, plain, ![X31]:(~v1_relat_1(X31)|k10_relat_1(X31,k2_relat_1(X31))=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.53/0.76  fof(c_0_66, plain, ![X36, X37, X38]:(~v1_relat_1(X38)|k10_relat_1(k7_relat_1(X38,X36),X37)=k3_xboole_0(X36,k10_relat_1(X38,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.53/0.76  fof(c_0_67, plain, ![X29, X30]:(~v1_relat_1(X30)|r1_tarski(k10_relat_1(X30,X29),k1_relat_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.53/0.76  fof(c_0_68, plain, ![X43, X44, X45]:(~v1_relat_1(X45)|~v1_funct_1(X45)|(~r1_tarski(X43,k1_relat_1(X45))|~r1_tarski(k9_relat_1(X45,X43),X44)|r1_tarski(X43,k10_relat_1(X45,X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.53/0.76  cnf(c_0_69, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_61])).
% 0.53/0.76  cnf(c_0_70, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.53/0.76  cnf(c_0_71, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.53/0.76  fof(c_0_72, plain, ![X39, X40]:(~v1_relat_1(X40)|~v1_funct_1(X40)|(~r1_tarski(X39,k2_relat_1(X40))|k9_relat_1(X40,k10_relat_1(X40,X39))=X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.53/0.76  cnf(c_0_73, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.53/0.76  cnf(c_0_74, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.53/0.76  cnf(c_0_75, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.53/0.76  cnf(c_0_76, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.53/0.76  cnf(c_0_77, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.53/0.76  cnf(c_0_78, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.53/0.76  cnf(c_0_79, negated_conjecture, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.53/0.76  cnf(c_0_80, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.53/0.76  cnf(c_0_81, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_28]), c_0_34]), c_0_35])).
% 0.53/0.76  cnf(c_0_82, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.53/0.76  cnf(c_0_83, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_45]), c_0_74]), c_0_54])])).
% 0.53/0.76  cnf(c_0_84, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_28]), c_0_34]), c_0_35])).
% 0.53/0.76  cnf(c_0_85, plain, (k1_relat_1(X1)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.53/0.76  cnf(c_0_86, negated_conjecture, (r1_tarski(X1,k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0))|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_54]), c_0_74])])).
% 0.53/0.76  cnf(c_0_87, plain, (k2_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),k6_relat_1(X2)))=k9_relat_1(X1,k10_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_81, c_0_48])).
% 0.53/0.76  cnf(c_0_88, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_80]), c_0_54]), c_0_45]), c_0_63])])).
% 0.53/0.76  cnf(c_0_89, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_48])).
% 0.53/0.76  cnf(c_0_90, plain, (k2_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X1,X2)),k6_relat_1(X3)))=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_84, c_0_48])).
% 0.53/0.76  cnf(c_0_91, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k10_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_74]), c_0_54]), c_0_74]), c_0_63])])).
% 0.53/0.76  cnf(c_0_92, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_74]), c_0_88]), c_0_80]), c_0_54])])).
% 0.53/0.76  cnf(c_0_93, plain, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_53]), c_0_54])])).
% 0.53/0.76  cnf(c_0_94, negated_conjecture, (k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1))=k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_54])]), c_0_92])).
% 0.53/0.76  cnf(c_0_95, plain, (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_59]), c_0_54])])).
% 0.53/0.76  cnf(c_0_96, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_54, c_0_46])).
% 0.53/0.76  cnf(c_0_97, negated_conjecture, (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0),esk2_0)=k10_relat_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_91]), c_0_88])).
% 0.53/0.76  cnf(c_0_98, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_74, c_0_95])).
% 0.53/0.76  cnf(c_0_99, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_53]), c_0_54])])).
% 0.53/0.76  cnf(c_0_100, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_83]), c_0_54])])).
% 0.53/0.76  cnf(c_0_101, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_45, c_0_95])).
% 0.53/0.76  cnf(c_0_102, negated_conjecture, (k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k10_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_97]), c_0_98]), c_0_99]), c_0_98]), c_0_70])])).
% 0.53/0.76  cnf(c_0_103, plain, (k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k9_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_53]), c_0_101]), c_0_54])])).
% 0.53/0.76  cnf(c_0_104, negated_conjecture, (k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k6_relat_1(k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_95, c_0_102])).
% 0.53/0.76  cnf(c_0_105, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k9_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[c_0_100, c_0_103])).
% 0.53/0.76  cnf(c_0_106, negated_conjecture, (k9_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0))=k10_relat_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_83])).
% 0.53/0.76  cnf(c_0_107, plain, (k9_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3))=k10_relat_1(k7_relat_1(X2,X1),X3)|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_90, c_0_105])).
% 0.53/0.76  cnf(c_0_108, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.53/0.76  cnf(c_0_109, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.53/0.76  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108])]), c_0_109]), ['proof']).
% 0.53/0.76  # SZS output end CNFRefutation
% 0.53/0.76  # Proof object total steps             : 111
% 0.53/0.76  # Proof object clause steps            : 68
% 0.53/0.76  # Proof object formula steps           : 43
% 0.53/0.76  # Proof object conjectures             : 16
% 0.53/0.76  # Proof object clause conjectures      : 13
% 0.53/0.76  # Proof object formula conjectures     : 3
% 0.53/0.76  # Proof object initial clauses used    : 26
% 0.53/0.76  # Proof object initial formulas used   : 21
% 0.53/0.76  # Proof object generating inferences   : 28
% 0.53/0.76  # Proof object simplifying inferences  : 79
% 0.53/0.76  # Training examples: 0 positive, 0 negative
% 0.53/0.76  # Parsed axioms                        : 21
% 0.53/0.76  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.76  # Initial clauses                      : 28
% 0.53/0.76  # Removed in clause preprocessing      : 5
% 0.53/0.76  # Initial clauses in saturation        : 23
% 0.53/0.76  # Processed clauses                    : 2613
% 0.53/0.76  # ...of these trivial                  : 31
% 0.53/0.76  # ...subsumed                          : 1824
% 0.53/0.76  # ...remaining for further processing  : 758
% 0.53/0.76  # Other redundant clauses eliminated   : 2
% 0.53/0.76  # Clauses deleted for lack of memory   : 0
% 0.53/0.76  # Backward-subsumed                    : 47
% 0.53/0.76  # Backward-rewritten                   : 70
% 0.53/0.76  # Generated clauses                    : 31269
% 0.53/0.76  # ...of the previous two non-trivial   : 29224
% 0.53/0.76  # Contextual simplify-reflections      : 4
% 0.53/0.76  # Paramodulations                      : 31267
% 0.53/0.76  # Factorizations                       : 0
% 0.53/0.76  # Equation resolutions                 : 2
% 0.53/0.76  # Propositional unsat checks           : 0
% 0.53/0.76  #    Propositional check models        : 0
% 0.53/0.76  #    Propositional check unsatisfiable : 0
% 0.53/0.76  #    Propositional clauses             : 0
% 0.53/0.76  #    Propositional clauses after purity: 0
% 0.53/0.76  #    Propositional unsat core size     : 0
% 0.53/0.76  #    Propositional preprocessing time  : 0.000
% 0.53/0.76  #    Propositional encoding time       : 0.000
% 0.53/0.76  #    Propositional solver time         : 0.000
% 0.53/0.76  #    Success case prop preproc time    : 0.000
% 0.53/0.76  #    Success case prop encoding time   : 0.000
% 0.53/0.76  #    Success case prop solver time     : 0.000
% 0.53/0.76  # Current number of processed clauses  : 617
% 0.53/0.76  #    Positive orientable unit clauses  : 105
% 0.53/0.76  #    Positive unorientable unit clauses: 0
% 0.53/0.76  #    Negative unit clauses             : 1
% 0.53/0.76  #    Non-unit-clauses                  : 511
% 0.53/0.76  # Current number of unprocessed clauses: 26396
% 0.53/0.76  # ...number of literals in the above   : 79599
% 0.53/0.76  # Current number of archived formulas  : 0
% 0.53/0.76  # Current number of archived clauses   : 144
% 0.53/0.76  # Clause-clause subsumption calls (NU) : 106901
% 0.53/0.76  # Rec. Clause-clause subsumption calls : 70200
% 0.53/0.76  # Non-unit clause-clause subsumptions  : 1874
% 0.53/0.76  # Unit Clause-clause subsumption calls : 127
% 0.53/0.76  # Rewrite failures with RHS unbound    : 0
% 0.53/0.76  # BW rewrite match attempts            : 512
% 0.53/0.76  # BW rewrite match successes           : 59
% 0.53/0.76  # Condensation attempts                : 0
% 0.53/0.76  # Condensation successes               : 0
% 0.53/0.76  # Termbank termtop insertions          : 571414
% 0.53/0.77  
% 0.53/0.77  # -------------------------------------------------
% 0.53/0.77  # User time                : 0.414 s
% 0.53/0.77  # System time              : 0.018 s
% 0.53/0.77  # Total time               : 0.433 s
% 0.53/0.77  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
