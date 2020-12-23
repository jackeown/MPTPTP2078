%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:45 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 532 expanded)
%              Number of clauses        :   72 ( 239 expanded)
%              Number of leaves         :   20 ( 133 expanded)
%              Depth                    :   25
%              Number of atoms          :  249 (1251 expanded)
%              Number of equality atoms :   44 ( 228 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k2_xboole_0(X14,X15),X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k2_xboole_0(X17,X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k3_xboole_0(X8,X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_26,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X4))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_35,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_36,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | r1_tarski(k10_relat_1(X34,X33),k1_relat_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | r1_tarski(k10_relat_1(X37,X36),k10_relat_1(X37,k2_relat_1(X37))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

fof(c_0_41,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k10_relat_1(X35,k2_relat_1(X35)) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | ~ r1_tarski(X28,X27)
      | r1_tarski(k2_xboole_0(X26,X28),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,k10_relat_1(X3,X4))
    | ~ r1_tarski(X1,k10_relat_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

fof(c_0_55,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk1_0),k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_52])])).

fof(c_0_57,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | r1_tarski(X11,k2_xboole_0(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_56])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_63,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,k3_xboole_0(X20,X21))
      | r1_tarski(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_64,plain,(
    ! [X44,X45,X46] :
      ( ~ v1_relat_1(X46)
      | k10_relat_1(k7_relat_1(X46,X44),X45) = k3_xboole_0(X44,k10_relat_1(X46,X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_65,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | v1_relat_1(k7_relat_1(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_46]),c_0_52])])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_61])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_49]),c_0_45])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_70,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | k2_relat_1(k7_relat_1(X32,X31)) = k9_relat_1(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_71,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k10_relat_1(esk2_0,X1) = k1_relat_1(esk2_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_66])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_45])).

cnf(c_0_76,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_77,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | r1_tarski(k1_relat_1(k7_relat_1(X41,X40)),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_xboole_0(X1,k10_relat_1(X2,X3)),k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_71]),c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_52])])).

cnf(c_0_80,negated_conjecture,
    ( k10_relat_1(esk2_0,X1) = k1_relat_1(esk2_0)
    | ~ r1_tarski(X2,k10_relat_1(esk2_0,X1))
    | ~ r1_tarski(k1_relat_1(esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_66])).

cnf(c_0_81,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_29])).

cnf(c_0_82,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_76]),c_0_72])).

cnf(c_0_83,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k7_relat_1(esk2_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_52])])).

fof(c_0_85,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ r1_tarski(k1_relat_1(X43),X42)
      | k7_relat_1(X43,X42) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_86,negated_conjecture,
    ( k10_relat_1(esk2_0,X1) = k1_relat_1(esk2_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k3_xboole_0(X2,k10_relat_1(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_82])).

cnf(c_0_88,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(k7_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,X1)))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_33])).

fof(c_0_90,plain,(
    ! [X38,X39] :
      ( ( r1_tarski(k1_relat_1(X38),k1_relat_1(X39))
        | ~ r1_tarski(X38,X39)
        | ~ v1_relat_1(X39)
        | ~ v1_relat_1(X38) )
      & ( r1_tarski(k2_relat_1(X38),k2_relat_1(X39))
        | ~ r1_tarski(X38,X39)
        | ~ v1_relat_1(X39)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_91,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_76]),c_0_72])).

cnf(c_0_92,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)) = k1_relat_1(esk2_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_52])])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0))) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_52]),c_0_45])])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_96,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_45])])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X2),X1)
    | ~ r1_tarski(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_95]),c_0_52])])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_52])])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_30])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_52]),c_0_45])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_52])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(esk2_0,X1)))
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_30])).

cnf(c_0_104,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_74,c_0_83])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_45])])).

cnf(c_0_106,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_47]),c_0_72])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_52]),c_0_45])])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_52])])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_29])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk1_0,k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_71]),c_0_52])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:11:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.12/1.28  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.12/1.28  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.12/1.28  #
% 1.12/1.28  # Preprocessing time       : 0.027 s
% 1.12/1.28  # Presaturation interreduction done
% 1.12/1.28  
% 1.12/1.28  # Proof found!
% 1.12/1.28  # SZS status Theorem
% 1.12/1.28  # SZS output start CNFRefutation
% 1.12/1.28  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.12/1.28  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.12/1.28  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.12/1.28  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.12/1.28  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.12/1.28  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 1.12/1.28  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.12/1.28  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.12/1.28  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 1.12/1.28  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.12/1.28  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.12/1.28  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.12/1.28  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.12/1.28  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.12/1.28  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 1.12/1.28  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.12/1.28  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.12/1.28  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.12/1.28  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.12/1.28  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.12/1.28  fof(c_0_20, plain, ![X14, X15, X16]:(~r1_tarski(k2_xboole_0(X14,X15),X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 1.12/1.28  fof(c_0_21, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k2_xboole_0(X17,X18)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.12/1.28  cnf(c_0_22, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.12/1.28  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.12/1.28  fof(c_0_24, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_tarski(k3_xboole_0(X8,X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 1.12/1.28  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.12/1.28  fof(c_0_26, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.12/1.28  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.12/1.28  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.12/1.28  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.12/1.28  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.12/1.28  fof(c_0_31, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 1.12/1.28  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X4))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.12/1.28  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.12/1.28  fof(c_0_34, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 1.12/1.28  fof(c_0_35, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.12/1.28  fof(c_0_36, plain, ![X33, X34]:(~v1_relat_1(X34)|r1_tarski(k10_relat_1(X34,X33),k1_relat_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 1.12/1.28  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.12/1.28  cnf(c_0_38, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.12/1.28  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.12/1.28  fof(c_0_40, plain, ![X36, X37]:(~v1_relat_1(X37)|r1_tarski(k10_relat_1(X37,X36),k10_relat_1(X37,k2_relat_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 1.12/1.28  fof(c_0_41, plain, ![X35]:(~v1_relat_1(X35)|k10_relat_1(X35,k2_relat_1(X35))=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 1.12/1.28  cnf(c_0_42, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.12/1.28  fof(c_0_43, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|~r1_tarski(X28,X27)|r1_tarski(k2_xboole_0(X26,X28),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.12/1.28  cnf(c_0_44, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k1_relat_1(esk2_0),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.12/1.28  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 1.12/1.28  cnf(c_0_46, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.12/1.28  cnf(c_0_47, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.12/1.28  cnf(c_0_48, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_42])).
% 1.12/1.28  cnf(c_0_49, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.12/1.28  cnf(c_0_50, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.12/1.28  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.12/1.28  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.12/1.28  cnf(c_0_53, plain, (r1_tarski(k2_xboole_0(X1,X2),k1_relat_1(X3))|~v1_relat_1(X3)|~r1_tarski(X2,k10_relat_1(X3,X4))|~r1_tarski(X1,k10_relat_1(X3,X4))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.12/1.28  cnf(c_0_54, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 1.12/1.28  fof(c_0_55, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.12/1.28  cnf(c_0_56, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk1_0),k1_relat_1(esk2_0))|~r1_tarski(X1,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_52])])).
% 1.12/1.28  fof(c_0_57, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|r1_tarski(X11,k2_xboole_0(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 1.12/1.28  cnf(c_0_58, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.12/1.28  cnf(c_0_59, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.12/1.28  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(X1,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_56])).
% 1.12/1.28  cnf(c_0_61, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.12/1.28  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.12/1.28  fof(c_0_63, plain, ![X19, X20, X21]:(~r1_tarski(X19,k3_xboole_0(X20,X21))|r1_tarski(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 1.12/1.28  fof(c_0_64, plain, ![X44, X45, X46]:(~v1_relat_1(X46)|k10_relat_1(k7_relat_1(X46,X44),X45)=k3_xboole_0(X44,k10_relat_1(X46,X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 1.12/1.28  fof(c_0_65, plain, ![X29, X30]:(~v1_relat_1(X29)|v1_relat_1(k7_relat_1(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 1.12/1.28  cnf(c_0_66, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_46]), c_0_52])])).
% 1.12/1.28  cnf(c_0_67, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_58, c_0_61])).
% 1.12/1.28  cnf(c_0_68, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_49]), c_0_45])])).
% 1.12/1.28  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.12/1.28  fof(c_0_70, plain, ![X31, X32]:(~v1_relat_1(X32)|k2_relat_1(k7_relat_1(X32,X31))=k9_relat_1(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 1.12/1.28  cnf(c_0_71, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.12/1.28  cnf(c_0_72, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.12/1.28  cnf(c_0_73, negated_conjecture, (k10_relat_1(esk2_0,X1)=k1_relat_1(esk2_0)|~r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_58, c_0_66])).
% 1.12/1.28  cnf(c_0_74, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.12/1.28  cnf(c_0_75, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_69, c_0_45])).
% 1.12/1.28  cnf(c_0_76, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.12/1.28  fof(c_0_77, plain, ![X40, X41]:(~v1_relat_1(X41)|r1_tarski(k1_relat_1(k7_relat_1(X41,X40)),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 1.12/1.28  cnf(c_0_78, plain, (r1_tarski(k3_xboole_0(X1,k10_relat_1(X2,X3)),k1_relat_1(k7_relat_1(X2,X1)))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_71]), c_0_72])).
% 1.12/1.28  cnf(c_0_79, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_51]), c_0_52])])).
% 1.12/1.28  cnf(c_0_80, negated_conjecture, (k10_relat_1(esk2_0,X1)=k1_relat_1(esk2_0)|~r1_tarski(X2,k10_relat_1(esk2_0,X1))|~r1_tarski(k1_relat_1(esk2_0),X2)), inference(spm,[status(thm)],[c_0_74, c_0_66])).
% 1.12/1.28  cnf(c_0_81, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_75, c_0_29])).
% 1.12/1.28  cnf(c_0_82, plain, (k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_76]), c_0_72])).
% 1.12/1.28  cnf(c_0_83, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.12/1.28  cnf(c_0_84, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k7_relat_1(esk2_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_52])])).
% 1.12/1.28  fof(c_0_85, plain, ![X42, X43]:(~v1_relat_1(X43)|(~r1_tarski(k1_relat_1(X43),X42)|k7_relat_1(X43,X42)=X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 1.12/1.28  cnf(c_0_86, negated_conjecture, (k10_relat_1(esk2_0,X1)=k1_relat_1(esk2_0)|~r1_tarski(k1_relat_1(esk2_0),k3_xboole_0(X2,k10_relat_1(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.12/1.28  cnf(c_0_87, plain, (k3_xboole_0(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_71, c_0_82])).
% 1.12/1.28  cnf(c_0_88, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(k7_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_58, c_0_83])).
% 1.12/1.28  cnf(c_0_89, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,X1)))|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_84, c_0_33])).
% 1.12/1.28  fof(c_0_90, plain, ![X38, X39]:((r1_tarski(k1_relat_1(X38),k1_relat_1(X39))|~r1_tarski(X38,X39)|~v1_relat_1(X39)|~v1_relat_1(X38))&(r1_tarski(k2_relat_1(X38),k2_relat_1(X39))|~r1_tarski(X38,X39)|~v1_relat_1(X39)|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 1.12/1.28  cnf(c_0_91, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_76]), c_0_72])).
% 1.12/1.28  cnf(c_0_92, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.12/1.28  cnf(c_0_93, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))=k1_relat_1(esk2_0)|~r1_tarski(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_52])])).
% 1.12/1.28  cnf(c_0_94, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0)))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_52]), c_0_45])])).
% 1.12/1.28  cnf(c_0_95, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 1.12/1.28  cnf(c_0_96, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 1.12/1.28  cnf(c_0_97, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_45])])).
% 1.12/1.28  cnf(c_0_98, negated_conjecture, (r1_tarski(esk1_0,X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X2),X1)|~r1_tarski(esk2_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_95]), c_0_52])])).
% 1.12/1.28  cnf(c_0_99, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_52])])).
% 1.12/1.28  cnf(c_0_100, plain, (r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X1)))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_78, c_0_30])).
% 1.12/1.28  cnf(c_0_101, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_52]), c_0_45])])).
% 1.12/1.28  cnf(c_0_102, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_52])])).
% 1.12/1.28  cnf(c_0_103, negated_conjecture, (r1_tarski(X1,k1_relat_1(k7_relat_1(esk2_0,X1)))|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_84, c_0_30])).
% 1.12/1.28  cnf(c_0_104, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X3,k1_relat_1(k7_relat_1(X1,X2)))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_74, c_0_83])).
% 1.12/1.28  cnf(c_0_105, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_45])])).
% 1.12/1.28  cnf(c_0_106, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_47]), c_0_72])).
% 1.12/1.28  cnf(c_0_107, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_52]), c_0_45])])).
% 1.12/1.28  cnf(c_0_108, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_52])])).
% 1.12/1.28  cnf(c_0_109, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_69, c_0_29])).
% 1.12/1.28  cnf(c_0_110, negated_conjecture, (r1_tarski(esk1_0,k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_71]), c_0_52])])).
% 1.12/1.28  cnf(c_0_111, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.12/1.28  cnf(c_0_112, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111]), ['proof']).
% 1.12/1.28  # SZS output end CNFRefutation
% 1.12/1.28  # Proof object total steps             : 113
% 1.12/1.28  # Proof object clause steps            : 72
% 1.12/1.28  # Proof object formula steps           : 41
% 1.12/1.28  # Proof object conjectures             : 31
% 1.12/1.28  # Proof object clause conjectures      : 28
% 1.12/1.28  # Proof object formula conjectures     : 3
% 1.12/1.28  # Proof object initial clauses used    : 23
% 1.12/1.28  # Proof object initial formulas used   : 20
% 1.12/1.28  # Proof object generating inferences   : 48
% 1.12/1.28  # Proof object simplifying inferences  : 43
% 1.12/1.28  # Training examples: 0 positive, 0 negative
% 1.12/1.28  # Parsed axioms                        : 20
% 1.12/1.28  # Removed by relevancy pruning/SinE    : 0
% 1.12/1.28  # Initial clauses                      : 25
% 1.12/1.28  # Removed in clause preprocessing      : 0
% 1.12/1.28  # Initial clauses in saturation        : 25
% 1.12/1.28  # Processed clauses                    : 9836
% 1.12/1.28  # ...of these trivial                  : 74
% 1.12/1.28  # ...subsumed                          : 8167
% 1.12/1.28  # ...remaining for further processing  : 1595
% 1.12/1.28  # Other redundant clauses eliminated   : 2
% 1.12/1.28  # Clauses deleted for lack of memory   : 0
% 1.12/1.28  # Backward-subsumed                    : 63
% 1.12/1.28  # Backward-rewritten                   : 64
% 1.12/1.28  # Generated clauses                    : 78826
% 1.12/1.28  # ...of the previous two non-trivial   : 75881
% 1.12/1.28  # Contextual simplify-reflections      : 58
% 1.12/1.28  # Paramodulations                      : 78824
% 1.12/1.28  # Factorizations                       : 0
% 1.12/1.28  # Equation resolutions                 : 2
% 1.12/1.28  # Propositional unsat checks           : 0
% 1.12/1.28  #    Propositional check models        : 0
% 1.12/1.28  #    Propositional check unsatisfiable : 0
% 1.12/1.28  #    Propositional clauses             : 0
% 1.12/1.28  #    Propositional clauses after purity: 0
% 1.12/1.28  #    Propositional unsat core size     : 0
% 1.12/1.28  #    Propositional preprocessing time  : 0.000
% 1.12/1.28  #    Propositional encoding time       : 0.000
% 1.12/1.28  #    Propositional solver time         : 0.000
% 1.12/1.28  #    Success case prop preproc time    : 0.000
% 1.12/1.28  #    Success case prop encoding time   : 0.000
% 1.12/1.28  #    Success case prop solver time     : 0.000
% 1.12/1.28  # Current number of processed clauses  : 1442
% 1.12/1.28  #    Positive orientable unit clauses  : 91
% 1.12/1.28  #    Positive unorientable unit clauses: 1
% 1.12/1.28  #    Negative unit clauses             : 51
% 1.12/1.28  #    Non-unit-clauses                  : 1299
% 1.12/1.28  # Current number of unprocessed clauses: 65720
% 1.12/1.28  # ...number of literals in the above   : 248085
% 1.12/1.28  # Current number of archived formulas  : 0
% 1.12/1.28  # Current number of archived clauses   : 151
% 1.12/1.28  # Clause-clause subsumption calls (NU) : 1166922
% 1.12/1.28  # Rec. Clause-clause subsumption calls : 182903
% 1.12/1.28  # Non-unit clause-clause subsumptions  : 5590
% 1.12/1.28  # Unit Clause-clause subsumption calls : 13363
% 1.12/1.28  # Rewrite failures with RHS unbound    : 0
% 1.12/1.28  # BW rewrite match attempts            : 529
% 1.12/1.28  # BW rewrite match successes           : 23
% 1.12/1.28  # Condensation attempts                : 0
% 1.12/1.28  # Condensation successes               : 0
% 1.12/1.28  # Termbank termtop insertions          : 1184113
% 1.12/1.28  
% 1.12/1.28  # -------------------------------------------------
% 1.12/1.28  # User time                : 0.910 s
% 1.12/1.28  # System time              : 0.037 s
% 1.12/1.28  # Total time               : 0.947 s
% 1.12/1.28  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
