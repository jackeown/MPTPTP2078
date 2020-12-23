%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:42 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 675 expanded)
%              Number of clauses        :   65 ( 312 expanded)
%              Number of leaves         :   19 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 (1041 expanded)
%              Number of equality atoms :   58 ( 428 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_19,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | X18 = k2_xboole_0(X17,k4_xboole_0(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_20,plain,(
    ! [X25,X26] : k3_tarski(k2_tarski(X25,X26)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_22,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_25,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_27,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,k2_xboole_0(X12,X13))
      | r1_tarski(k4_xboole_0(X11,X12),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_tarski(X24,X23) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_30,plain,
    ( X2 = k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_44,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | k10_relat_1(k7_relat_1(X42,X40),X41) = k3_xboole_0(X40,k10_relat_1(X42,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_45,plain,(
    ! [X27,X28] : k1_setfam_1(k2_tarski(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_46,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_47,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k10_relat_1(X35,k2_relat_1(X35)) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_55,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | v1_relat_1(k7_relat_1(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_31])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_60,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_62,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_52])).

cnf(c_0_64,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2))) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_37])).

fof(c_0_70,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(k1_relat_1(k7_relat_1(X39,X38)),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_71,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | r1_tarski(k10_relat_1(X37,X36),k10_relat_1(X37,k2_relat_1(X37))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

cnf(c_0_72,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_65]),c_0_66]),c_0_47])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),X1)) = k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1))) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,k4_xboole_0(esk1_0,X1)),k2_relat_1(esk2_0)) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_73]),c_0_32]),c_0_69]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_61])).

fof(c_0_80,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(X33,X34)
      | k9_relat_1(k7_relat_1(X32,X34),X33) = k9_relat_1(X32,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_49])).

fof(c_0_83,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | k9_relat_1(X31,k1_relat_1(X31)) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k1_relat_1(k7_relat_1(esk2_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_72]),c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(esk2_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_79])).

cnf(c_0_87,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_63])).

cnf(c_0_90,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_86]),c_0_66]),c_0_47])).

cnf(c_0_93,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_37])).

cnf(c_0_95,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1))) = k2_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_72])).

cnf(c_0_96,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_91]),c_0_92]),c_0_47])).

cnf(c_0_97,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),X1) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_61])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,esk1_0)) = k9_relat_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_67])).

cnf(c_0_101,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_99]),c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:51:35 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.42  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.18/0.42  # and selection function SelectDiffNegLit.
% 0.18/0.42  #
% 0.18/0.42  # Preprocessing time       : 0.028 s
% 0.18/0.42  # Presaturation interreduction done
% 0.18/0.42  
% 0.18/0.42  # Proof found!
% 0.18/0.42  # SZS status Theorem
% 0.18/0.42  # SZS output start CNFRefutation
% 0.18/0.42  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.18/0.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.18/0.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.18/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.42  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.42  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.18/0.42  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.18/0.42  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.18/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.42  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.18/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.18/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.18/0.42  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.18/0.42  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.18/0.42  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.18/0.42  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 0.18/0.42  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.18/0.42  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.18/0.42  fof(c_0_19, plain, ![X17, X18]:(~r1_tarski(X17,X18)|X18=k2_xboole_0(X17,k4_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.18/0.42  fof(c_0_20, plain, ![X25, X26]:k3_tarski(k2_tarski(X25,X26))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.18/0.42  fof(c_0_21, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.18/0.42  cnf(c_0_22, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.42  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.42  fof(c_0_24, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.42  fof(c_0_25, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.42  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.18/0.42  fof(c_0_27, plain, ![X11, X12, X13]:(~r1_tarski(X11,k2_xboole_0(X12,X13))|r1_tarski(k4_xboole_0(X11,X12),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.18/0.42  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.42  fof(c_0_29, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_tarski(X24,X23), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.18/0.42  cnf(c_0_30, plain, (X2=k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.42  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.42  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.42  fof(c_0_33, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.42  fof(c_0_34, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.18/0.42  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.42  cnf(c_0_36, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_23])).
% 0.18/0.42  cnf(c_0_37, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.42  cnf(c_0_38, plain, (k3_tarski(k2_tarski(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.18/0.42  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.42  cnf(c_0_40, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.42  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_35, c_0_23])).
% 0.18/0.42  cnf(c_0_42, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.42  fof(c_0_43, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.42  fof(c_0_44, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|k10_relat_1(k7_relat_1(X42,X40),X41)=k3_xboole_0(X40,k10_relat_1(X42,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.18/0.42  fof(c_0_45, plain, ![X27, X28]:k1_setfam_1(k2_tarski(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.18/0.42  fof(c_0_46, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.18/0.42  cnf(c_0_47, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.18/0.42  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.18/0.42  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.42  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.42  cnf(c_0_51, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.42  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.42  fof(c_0_53, plain, ![X35]:(~v1_relat_1(X35)|k10_relat_1(X35,k2_relat_1(X35))=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.18/0.42  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.42  fof(c_0_55, plain, ![X29, X30]:(~v1_relat_1(X29)|v1_relat_1(k7_relat_1(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.18/0.42  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 0.18/0.42  cnf(c_0_57, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.18/0.42  cnf(c_0_58, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_31])).
% 0.18/0.42  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_31])).
% 0.18/0.42  cnf(c_0_60, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.42  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.42  cnf(c_0_62, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.42  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_54, c_0_52])).
% 0.18/0.42  cnf(c_0_64, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.42  cnf(c_0_65, negated_conjecture, (r1_tarski(k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.42  cnf(c_0_66, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.42  cnf(c_0_67, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2)))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.42  cnf(c_0_68, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_61])).
% 0.18/0.42  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_63, c_0_37])).
% 0.18/0.42  fof(c_0_70, plain, ![X38, X39]:(~v1_relat_1(X39)|r1_tarski(k1_relat_1(k7_relat_1(X39,X38)),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.18/0.42  fof(c_0_71, plain, ![X36, X37]:(~v1_relat_1(X37)|r1_tarski(k10_relat_1(X37,X36),k10_relat_1(X37,k2_relat_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.18/0.42  cnf(c_0_72, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_64, c_0_61])).
% 0.18/0.42  cnf(c_0_73, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_65]), c_0_66]), c_0_47])).
% 0.18/0.42  cnf(c_0_74, negated_conjecture, (k4_xboole_0(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),X1))=k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.18/0.42  cnf(c_0_75, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.18/0.42  cnf(c_0_76, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.18/0.42  cnf(c_0_77, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1)))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_62, c_0_72])).
% 0.18/0.42  cnf(c_0_78, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,k4_xboole_0(esk1_0,X1)),k2_relat_1(esk2_0))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_73]), c_0_32]), c_0_69]), c_0_74])).
% 0.18/0.42  cnf(c_0_79, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_75, c_0_61])).
% 0.18/0.42  fof(c_0_80, plain, ![X32, X33, X34]:(~v1_relat_1(X32)|(~r1_tarski(X33,X34)|k9_relat_1(k7_relat_1(X32,X34),X33)=k9_relat_1(X32,X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.18/0.42  cnf(c_0_81, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.42  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_39, c_0_49])).
% 0.18/0.42  fof(c_0_83, plain, ![X31]:(~v1_relat_1(X31)|k9_relat_1(X31,k1_relat_1(X31))=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.18/0.42  cnf(c_0_84, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k1_relat_1(k7_relat_1(esk2_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_72]), c_0_77])).
% 0.18/0.42  cnf(c_0_85, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(esk2_0))=esk1_0), inference(spm,[status(thm)],[c_0_78, c_0_32])).
% 0.18/0.42  cnf(c_0_86, negated_conjecture, (r1_tarski(k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_79])).
% 0.18/0.42  cnf(c_0_87, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.18/0.42  cnf(c_0_88, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_81])).
% 0.18/0.42  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_82, c_0_63])).
% 0.18/0.42  cnf(c_0_90, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.18/0.42  cnf(c_0_91, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.18/0.42  cnf(c_0_92, negated_conjecture, (k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_86]), c_0_66]), c_0_47])).
% 0.18/0.42  cnf(c_0_93, plain, (k9_relat_1(k7_relat_1(X1,X2),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.18/0.42  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_89, c_0_37])).
% 0.18/0.42  cnf(c_0_95, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1)))=k2_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_90, c_0_72])).
% 0.18/0.42  cnf(c_0_96, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_91]), c_0_92]), c_0_47])).
% 0.18/0.42  cnf(c_0_97, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),X1)=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_93, c_0_61])).
% 0.18/0.42  cnf(c_0_98, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_94, c_0_88])).
% 0.18/0.42  cnf(c_0_99, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,esk1_0))=k9_relat_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 0.18/0.42  cnf(c_0_100, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_98, c_0_67])).
% 0.18/0.42  cnf(c_0_101, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_99]), c_0_96])).
% 0.18/0.42  cnf(c_0_102, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.42  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), ['proof']).
% 0.18/0.42  # SZS output end CNFRefutation
% 0.18/0.42  # Proof object total steps             : 104
% 0.18/0.42  # Proof object clause steps            : 65
% 0.18/0.42  # Proof object formula steps           : 39
% 0.18/0.42  # Proof object conjectures             : 29
% 0.18/0.42  # Proof object clause conjectures      : 26
% 0.18/0.42  # Proof object formula conjectures     : 3
% 0.18/0.42  # Proof object initial clauses used    : 22
% 0.18/0.42  # Proof object initial formulas used   : 19
% 0.18/0.42  # Proof object generating inferences   : 37
% 0.18/0.42  # Proof object simplifying inferences  : 21
% 0.18/0.42  # Training examples: 0 positive, 0 negative
% 0.18/0.42  # Parsed axioms                        : 20
% 0.18/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.42  # Initial clauses                      : 24
% 0.18/0.42  # Removed in clause preprocessing      : 2
% 0.18/0.42  # Initial clauses in saturation        : 22
% 0.18/0.42  # Processed clauses                    : 838
% 0.18/0.42  # ...of these trivial                  : 58
% 0.18/0.42  # ...subsumed                          : 463
% 0.18/0.42  # ...remaining for further processing  : 317
% 0.18/0.42  # Other redundant clauses eliminated   : 2
% 0.18/0.42  # Clauses deleted for lack of memory   : 0
% 0.18/0.42  # Backward-subsumed                    : 11
% 0.18/0.42  # Backward-rewritten                   : 50
% 0.18/0.42  # Generated clauses                    : 4312
% 0.18/0.42  # ...of the previous two non-trivial   : 3071
% 0.18/0.42  # Contextual simplify-reflections      : 0
% 0.18/0.42  # Paramodulations                      : 4310
% 0.18/0.42  # Factorizations                       : 0
% 0.18/0.42  # Equation resolutions                 : 2
% 0.18/0.42  # Propositional unsat checks           : 0
% 0.18/0.42  #    Propositional check models        : 0
% 0.18/0.42  #    Propositional check unsatisfiable : 0
% 0.18/0.42  #    Propositional clauses             : 0
% 0.18/0.42  #    Propositional clauses after purity: 0
% 0.18/0.42  #    Propositional unsat core size     : 0
% 0.18/0.42  #    Propositional preprocessing time  : 0.000
% 0.18/0.42  #    Propositional encoding time       : 0.000
% 0.18/0.42  #    Propositional solver time         : 0.000
% 0.18/0.42  #    Success case prop preproc time    : 0.000
% 0.18/0.42  #    Success case prop encoding time   : 0.000
% 0.18/0.42  #    Success case prop solver time     : 0.000
% 0.18/0.42  # Current number of processed clauses  : 233
% 0.18/0.42  #    Positive orientable unit clauses  : 131
% 0.18/0.42  #    Positive unorientable unit clauses: 3
% 0.18/0.42  #    Negative unit clauses             : 1
% 0.18/0.42  #    Non-unit-clauses                  : 98
% 0.18/0.42  # Current number of unprocessed clauses: 2183
% 0.18/0.42  # ...number of literals in the above   : 2531
% 0.18/0.42  # Current number of archived formulas  : 0
% 0.18/0.42  # Current number of archived clauses   : 84
% 0.18/0.42  # Clause-clause subsumption calls (NU) : 6980
% 0.18/0.42  # Rec. Clause-clause subsumption calls : 4229
% 0.18/0.42  # Non-unit clause-clause subsumptions  : 473
% 0.18/0.42  # Unit Clause-clause subsumption calls : 79
% 0.18/0.42  # Rewrite failures with RHS unbound    : 0
% 0.18/0.42  # BW rewrite match attempts            : 369
% 0.18/0.42  # BW rewrite match successes           : 53
% 0.18/0.42  # Condensation attempts                : 0
% 0.18/0.42  # Condensation successes               : 0
% 0.18/0.42  # Termbank termtop insertions          : 51507
% 0.18/0.43  
% 0.18/0.43  # -------------------------------------------------
% 0.18/0.43  # User time                : 0.087 s
% 0.18/0.43  # System time              : 0.006 s
% 0.18/0.43  # Total time               : 0.093 s
% 0.18/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
