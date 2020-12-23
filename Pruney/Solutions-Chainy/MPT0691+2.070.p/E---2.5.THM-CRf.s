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
% DateTime   : Thu Dec  3 10:54:51 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 227 expanded)
%              Number of clauses        :   52 (  97 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 537 expanded)
%              Number of equality atoms :   39 (  95 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

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

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X16,X15)
      | r1_tarski(k2_xboole_0(X14,X16),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k10_relat_1(X26,X24),k10_relat_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

fof(c_0_20,plain,(
    ! [X12,X13] : r1_tarski(X12,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_24,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(X6,k2_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k10_relat_1(X23,k2_relat_1(X23)) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

fof(c_0_36,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(X31,k1_relat_1(X32))
      | k1_relat_1(k7_relat_1(X32,X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_37,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | k1_relat_1(k7_relat_1(X30,X29)) = k3_xboole_0(k1_relat_1(X30),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_38,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | k10_relat_1(k7_relat_1(X37,X35),X36) = k3_xboole_0(X35,k10_relat_1(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,k1_relat_1(esk2_0)),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

fof(c_0_42,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(k1_relat_1(X34),X33)
      | k7_relat_1(X34,X33) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk1_0),k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_30])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_xboole_0(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26])])).

cnf(c_0_46,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_50,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k7_relat_1(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_51,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k2_xboole_0(X3,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(esk1_0,k1_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_40]),c_0_41])])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_relat_1(esk2_0),esk1_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_47])])).

cnf(c_0_57,plain,
    ( k10_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3) = k1_relat_1(k7_relat_1(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_47])])).

cnf(c_0_60,plain,
    ( k7_relat_1(X1,k2_xboole_0(k1_relat_1(X1),X2)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk2_0),esk1_0) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_54]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(k7_relat_1(esk2_0,esk1_0))))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),esk1_0)
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(esk1_0,X1) = k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k1_relat_1(k7_relat_1(X2,k10_relat_1(X3,X4)))) = k10_relat_1(k7_relat_1(k7_relat_1(X3,k1_relat_1(X2)),X1),X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_57]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k10_relat_1(esk2_0,X1))) = k10_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_59]),c_0_47])])).

cnf(c_0_67,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_47])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(k7_relat_1(esk2_0,esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_58]),c_0_47])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58]),c_0_47])])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk1_0,X1) = k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_58]),c_0_47])])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(X1,k10_relat_1(esk2_0,X2)) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_47])])).

fof(c_0_72,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k2_relat_1(k7_relat_1(X20,X19)) = k9_relat_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_73,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_74,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(k7_relat_1(esk2_0,esk1_0))) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_68]),c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1) = k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_77,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,k2_relat_1(k7_relat_1(esk2_0,esk1_0))))) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(k7_relat_1(esk2_0,esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_47])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_58]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:11:35 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.92/1.08  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.92/1.08  # and selection function SelectCQIPrecWNTNp.
% 0.92/1.08  #
% 0.92/1.08  # Preprocessing time       : 0.028 s
% 0.92/1.08  # Presaturation interreduction done
% 0.92/1.08  
% 0.92/1.08  # Proof found!
% 0.92/1.08  # SZS status Theorem
% 0.92/1.08  # SZS output start CNFRefutation
% 0.92/1.08  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.92/1.08  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.92/1.08  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.92/1.08  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 0.92/1.08  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.92/1.08  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.92/1.08  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.92/1.08  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.92/1.08  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.92/1.08  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.92/1.08  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.92/1.08  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.92/1.08  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.92/1.08  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.92/1.08  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.92/1.08  fof(c_0_15, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.92/1.08  fof(c_0_16, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X16,X15)|r1_tarski(k2_xboole_0(X14,X16),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.92/1.08  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.92/1.08  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.92/1.08  fof(c_0_19, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X24,X25)|r1_tarski(k10_relat_1(X26,X24),k10_relat_1(X26,X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 0.92/1.08  fof(c_0_20, plain, ![X12, X13]:r1_tarski(X12,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.92/1.08  cnf(c_0_21, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.92/1.08  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.92/1.08  fof(c_0_23, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.92/1.08  fof(c_0_24, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.92/1.08  cnf(c_0_25, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.92/1.08  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.92/1.08  fof(c_0_27, plain, ![X23]:(~v1_relat_1(X23)|k10_relat_1(X23,k2_relat_1(X23))=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.92/1.08  cnf(c_0_28, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.92/1.08  fof(c_0_29, plain, ![X21, X22]:(~v1_relat_1(X22)|r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.92/1.08  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.08  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.08  cnf(c_0_32, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.92/1.08  cnf(c_0_33, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.92/1.08  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.92/1.08  cnf(c_0_35, plain, (r1_tarski(k2_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.92/1.08  fof(c_0_36, plain, ![X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(X31,k1_relat_1(X32))|k1_relat_1(k7_relat_1(X32,X31))=X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.92/1.08  fof(c_0_37, plain, ![X29, X30]:(~v1_relat_1(X30)|k1_relat_1(k7_relat_1(X30,X29))=k3_xboole_0(k1_relat_1(X30),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.92/1.08  fof(c_0_38, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|k10_relat_1(k7_relat_1(X37,X35),X36)=k3_xboole_0(X35,k10_relat_1(X37,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.92/1.08  cnf(c_0_39, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.92/1.08  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_xboole_0(esk1_0,k1_relat_1(esk2_0)),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.92/1.08  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 0.92/1.08  fof(c_0_42, plain, ![X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(k1_relat_1(X34),X33)|k7_relat_1(X34,X33)=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.92/1.08  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk1_0),k1_relat_1(esk2_0))|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_21, c_0_30])).
% 0.92/1.08  cnf(c_0_44, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_xboole_0(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.92/1.08  cnf(c_0_45, plain, (k2_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_26])])).
% 0.92/1.08  cnf(c_0_46, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.08  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.08  cnf(c_0_48, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.92/1.08  cnf(c_0_49, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.92/1.08  fof(c_0_50, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k7_relat_1(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.92/1.08  cnf(c_0_51, plain, (r1_tarski(k10_relat_1(X1,X2),k2_xboole_0(X3,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_39])).
% 0.92/1.08  cnf(c_0_52, negated_conjecture, (k2_xboole_0(esk1_0,k1_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_40]), c_0_41])])).
% 0.92/1.08  cnf(c_0_53, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.92/1.08  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_xboole_0(k1_relat_1(esk2_0),esk1_0),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 0.92/1.08  cnf(c_0_55, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.92/1.08  cnf(c_0_56, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_30]), c_0_47])])).
% 0.92/1.08  cnf(c_0_57, plain, (k10_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3)=k1_relat_1(k7_relat_1(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.92/1.08  cnf(c_0_58, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.92/1.08  cnf(c_0_59, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_47])])).
% 0.92/1.08  cnf(c_0_60, plain, (k7_relat_1(X1,k2_xboole_0(k1_relat_1(X1),X2))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_26])).
% 0.92/1.08  cnf(c_0_61, negated_conjecture, (k2_xboole_0(k1_relat_1(esk2_0),esk1_0)=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_54]), c_0_26])])).
% 0.92/1.08  cnf(c_0_62, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(k7_relat_1(esk2_0,esk1_0))))|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.92/1.08  cnf(c_0_63, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),esk1_0)|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_56])).
% 0.92/1.08  cnf(c_0_64, negated_conjecture, (k3_xboole_0(esk1_0,X1)=k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1))|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_48, c_0_56])).
% 0.92/1.08  cnf(c_0_65, plain, (k3_xboole_0(X1,k1_relat_1(k7_relat_1(X2,k10_relat_1(X3,X4))))=k10_relat_1(k7_relat_1(k7_relat_1(X3,k1_relat_1(X2)),X1),X4)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_57]), c_0_58])).
% 0.92/1.08  cnf(c_0_66, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))=k10_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_59]), c_0_47])])).
% 0.92/1.08  cnf(c_0_67, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_47])])).
% 0.92/1.08  cnf(c_0_68, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(k7_relat_1(esk2_0,esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_58]), c_0_47])])).
% 0.92/1.08  cnf(c_0_69, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_58]), c_0_47])])).
% 0.92/1.08  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk1_0,X1)=k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_58]), c_0_47])])).
% 0.92/1.08  cnf(c_0_71, negated_conjecture, (k3_xboole_0(X1,k10_relat_1(esk2_0,X2))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_47])])).
% 0.92/1.08  fof(c_0_72, plain, ![X19, X20]:(~v1_relat_1(X20)|k2_relat_1(k7_relat_1(X20,X19))=k9_relat_1(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.92/1.08  fof(c_0_73, plain, ![X27, X28]:(~v1_relat_1(X28)|r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.92/1.08  cnf(c_0_74, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(k7_relat_1(esk2_0,esk1_0)))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_68]), c_0_69])])).
% 0.92/1.08  cnf(c_0_75, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1)=k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.92/1.08  cnf(c_0_76, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.08  cnf(c_0_77, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.92/1.08  cnf(c_0_78, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.92/1.08  cnf(c_0_79, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,k2_relat_1(k7_relat_1(esk2_0,esk1_0)))))=esk1_0), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.92/1.08  cnf(c_0_80, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(k7_relat_1(esk2_0,esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_47])])).
% 0.92/1.08  cnf(c_0_81, negated_conjecture, (~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.92/1.08  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_58]), c_0_47])]), ['proof']).
% 0.92/1.08  # SZS output end CNFRefutation
% 0.92/1.08  # Proof object total steps             : 83
% 0.92/1.08  # Proof object clause steps            : 52
% 0.92/1.08  # Proof object formula steps           : 31
% 0.92/1.08  # Proof object conjectures             : 28
% 0.92/1.08  # Proof object clause conjectures      : 25
% 0.92/1.08  # Proof object formula conjectures     : 3
% 0.92/1.08  # Proof object initial clauses used    : 18
% 0.92/1.08  # Proof object initial formulas used   : 15
% 0.92/1.08  # Proof object generating inferences   : 32
% 0.92/1.08  # Proof object simplifying inferences  : 33
% 0.92/1.08  # Training examples: 0 positive, 0 negative
% 0.92/1.08  # Parsed axioms                        : 16
% 0.92/1.08  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.08  # Initial clauses                      : 20
% 0.92/1.08  # Removed in clause preprocessing      : 0
% 0.92/1.08  # Initial clauses in saturation        : 20
% 0.92/1.08  # Processed clauses                    : 6872
% 0.92/1.08  # ...of these trivial                  : 562
% 0.92/1.08  # ...subsumed                          : 4866
% 0.92/1.08  # ...remaining for further processing  : 1444
% 0.92/1.08  # Other redundant clauses eliminated   : 2
% 0.92/1.08  # Clauses deleted for lack of memory   : 0
% 0.92/1.08  # Backward-subsumed                    : 25
% 0.92/1.08  # Backward-rewritten                   : 197
% 0.92/1.08  # Generated clauses                    : 98847
% 0.92/1.08  # ...of the previous two non-trivial   : 76423
% 0.92/1.08  # Contextual simplify-reflections      : 73
% 0.92/1.08  # Paramodulations                      : 98845
% 0.92/1.08  # Factorizations                       : 0
% 0.92/1.08  # Equation resolutions                 : 2
% 0.92/1.08  # Propositional unsat checks           : 0
% 0.92/1.08  #    Propositional check models        : 0
% 0.92/1.08  #    Propositional check unsatisfiable : 0
% 0.92/1.08  #    Propositional clauses             : 0
% 0.92/1.08  #    Propositional clauses after purity: 0
% 0.92/1.08  #    Propositional unsat core size     : 0
% 0.92/1.08  #    Propositional preprocessing time  : 0.000
% 0.92/1.08  #    Propositional encoding time       : 0.000
% 0.92/1.08  #    Propositional solver time         : 0.000
% 0.92/1.08  #    Success case prop preproc time    : 0.000
% 0.92/1.08  #    Success case prop encoding time   : 0.000
% 0.92/1.08  #    Success case prop solver time     : 0.000
% 0.92/1.08  # Current number of processed clauses  : 1201
% 0.92/1.08  #    Positive orientable unit clauses  : 337
% 0.92/1.08  #    Positive unorientable unit clauses: 1
% 0.92/1.08  #    Negative unit clauses             : 3
% 0.92/1.08  #    Non-unit-clauses                  : 860
% 0.92/1.08  # Current number of unprocessed clauses: 69237
% 0.92/1.08  # ...number of literals in the above   : 161076
% 0.92/1.08  # Current number of archived formulas  : 0
% 0.92/1.08  # Current number of archived clauses   : 241
% 0.92/1.08  # Clause-clause subsumption calls (NU) : 78978
% 0.92/1.08  # Rec. Clause-clause subsumption calls : 71413
% 0.92/1.08  # Non-unit clause-clause subsumptions  : 4953
% 0.92/1.08  # Unit Clause-clause subsumption calls : 1756
% 0.92/1.08  # Rewrite failures with RHS unbound    : 0
% 0.92/1.08  # BW rewrite match attempts            : 2403
% 0.92/1.08  # BW rewrite match successes           : 182
% 0.92/1.08  # Condensation attempts                : 0
% 0.92/1.08  # Condensation successes               : 0
% 0.92/1.08  # Termbank termtop insertions          : 1695483
% 0.92/1.09  
% 0.92/1.09  # -------------------------------------------------
% 0.92/1.09  # User time                : 0.738 s
% 0.92/1.09  # System time              : 0.032 s
% 0.92/1.09  # Total time               : 0.771 s
% 0.92/1.09  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
