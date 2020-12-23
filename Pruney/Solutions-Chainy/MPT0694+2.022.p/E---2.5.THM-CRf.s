%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:59 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 349 expanded)
%              Number of clauses        :   43 ( 151 expanded)
%              Number of leaves         :   10 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  131 ( 769 expanded)
%              Number of equality atoms :   35 ( 208 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t101_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X1),X1) = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t149_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | k7_relat_1(k7_relat_1(X13,X12),X12) = k7_relat_1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X11)
      | k7_relat_1(k7_relat_1(X11,X9),X10) = k7_relat_1(X11,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_12,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_13,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k3_xboole_0(X2,X3)) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_19,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)) ) ),
    inference(assume_negation,[status(cth)],[t149_funct_1])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k2_relat_1(k7_relat_1(X17,X16)) = k9_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_22,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,k3_xboole_0(X2,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_23,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X4)) = k7_relat_1(k7_relat_1(k7_relat_1(X1,X4),X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ( v1_relat_1(k7_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(k7_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_26,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_28,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_33,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_35,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,k3_xboole_0(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(esk3_0,k3_xboole_0(X1,X1)) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31])])).

fof(c_0_37,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k9_relat_1(X15,X14),k2_relat_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_38,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,k3_xboole_0(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_36]),c_0_31])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_15])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X2))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_47,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X3)) = k9_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(esk3_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_14]),c_0_31])])).

fof(c_0_49,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X22)
      | k10_relat_1(k7_relat_1(X22,X20),X21) = k3_xboole_0(X20,k10_relat_1(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k9_relat_1(esk3_0,esk1_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k9_relat_1(X1,X2))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_52,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | r1_tarski(k9_relat_1(X24,k10_relat_1(X24,X23)),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(X1,X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_48]),c_0_34])])).

cnf(c_0_54,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_34]),c_0_31])])).

cnf(c_0_57,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(X2,X3)) = k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(X2,X1),X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_36]),c_0_31])])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_36]),c_0_30]),c_0_31])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_31])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_34])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.42/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.42/0.60  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.42/0.60  #
% 0.42/0.60  # Preprocessing time       : 0.026 s
% 0.42/0.60  # Presaturation interreduction done
% 0.42/0.60  
% 0.42/0.60  # Proof found!
% 0.42/0.60  # SZS status Theorem
% 0.42/0.60  # SZS output start CNFRefutation
% 0.42/0.60  fof(t101_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(k7_relat_1(X2,X1),X1)=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_relat_1)).
% 0.42/0.60  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.42/0.60  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.42/0.60  fof(t149_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 0.42/0.60  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.42/0.60  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.42/0.60  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.42/0.60  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.42/0.60  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.42/0.60  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.42/0.60  fof(c_0_10, plain, ![X12, X13]:(~v1_relat_1(X13)|k7_relat_1(k7_relat_1(X13,X12),X12)=k7_relat_1(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).
% 0.42/0.60  fof(c_0_11, plain, ![X9, X10, X11]:(~v1_relat_1(X11)|k7_relat_1(k7_relat_1(X11,X9),X10)=k7_relat_1(X11,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.42/0.60  fof(c_0_12, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.42/0.60  cnf(c_0_13, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.42/0.60  cnf(c_0_14, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.60  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.60  cnf(c_0_16, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k3_xboole_0(X2,X3))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.42/0.60  cnf(c_0_17, plain, (k7_relat_1(X1,k3_xboole_0(X2,X3))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.42/0.60  cnf(c_0_18, plain, (k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,X2))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 0.42/0.60  cnf(c_0_19, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_17])).
% 0.42/0.60  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t149_funct_1])).
% 0.42/0.60  fof(c_0_21, plain, ![X16, X17]:(~v1_relat_1(X17)|k2_relat_1(k7_relat_1(X17,X16))=k9_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.42/0.60  cnf(c_0_22, plain, (k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,k3_xboole_0(X2,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_18])).
% 0.42/0.60  cnf(c_0_23, plain, (k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X4))=k7_relat_1(k7_relat_1(k7_relat_1(X1,X4),X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.42/0.60  fof(c_0_24, plain, ![X18, X19]:((v1_relat_1(k7_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(k7_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.42/0.60  fof(c_0_25, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.42/0.60  cnf(c_0_26, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.60  cnf(c_0_27, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.42/0.60  cnf(c_0_28, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.42/0.60  cnf(c_0_29, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.60  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  cnf(c_0_32, plain, (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))=k9_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_14])).
% 0.42/0.60  cnf(c_0_33, plain, (k7_relat_1(X1,k3_xboole_0(X2,X2))=k7_relat_1(X1,X2)|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.42/0.60  cnf(c_0_34, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.42/0.60  cnf(c_0_35, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,k3_xboole_0(X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_13])).
% 0.42/0.60  cnf(c_0_36, negated_conjecture, (k7_relat_1(esk3_0,k3_xboole_0(X1,X1))=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_31])])).
% 0.42/0.60  fof(c_0_37, plain, ![X14, X15]:(~v1_relat_1(X15)|r1_tarski(k9_relat_1(X15,X14),k2_relat_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.42/0.60  cnf(c_0_38, plain, (k9_relat_1(X1,k3_xboole_0(X2,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_35])).
% 0.42/0.60  cnf(c_0_39, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,k3_xboole_0(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_36]), c_0_31])])).
% 0.42/0.60  cnf(c_0_40, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  fof(c_0_41, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.42/0.60  cnf(c_0_42, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.60  cnf(c_0_43, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_31])])).
% 0.42/0.60  cnf(c_0_44, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0)))), inference(rw,[status(thm)],[c_0_40, c_0_15])).
% 0.42/0.60  cnf(c_0_45, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.42/0.60  cnf(c_0_46, plain, (r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X2))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_26])).
% 0.42/0.60  cnf(c_0_47, plain, (k9_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X3))=k9_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_35])).
% 0.42/0.60  cnf(c_0_48, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(esk3_0,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_14]), c_0_31])])).
% 0.42/0.60  fof(c_0_49, plain, ![X20, X21, X22]:(~v1_relat_1(X22)|k10_relat_1(k7_relat_1(X22,X20),X21)=k3_xboole_0(X20,k10_relat_1(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.42/0.60  cnf(c_0_50, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k9_relat_1(esk3_0,esk1_0))|~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.42/0.60  cnf(c_0_51, plain, (r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k9_relat_1(X1,X2))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.42/0.60  fof(c_0_52, plain, ![X23, X24]:(~v1_relat_1(X24)|~v1_funct_1(X24)|r1_tarski(k9_relat_1(X24,k10_relat_1(X24,X23)),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.42/0.60  cnf(c_0_53, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(X1,X2))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_48]), c_0_34])])).
% 0.42/0.60  cnf(c_0_54, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.42/0.60  cnf(c_0_55, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.60  cnf(c_0_56, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_34]), c_0_31])])).
% 0.42/0.60  cnf(c_0_57, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.42/0.60  cnf(c_0_58, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(X2,X3))=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(X2,X1),X3))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.60  cnf(c_0_59, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),X1)=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_36]), c_0_31])])).
% 0.42/0.60  cnf(c_0_60, negated_conjecture, (v1_funct_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_36]), c_0_30]), c_0_31])])).
% 0.42/0.60  cnf(c_0_61, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_54]), c_0_31])])).
% 0.42/0.60  cnf(c_0_62, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_34])])).
% 0.42/0.60  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])]), ['proof']).
% 0.42/0.60  # SZS output end CNFRefutation
% 0.42/0.60  # Proof object total steps             : 64
% 0.42/0.60  # Proof object clause steps            : 43
% 0.42/0.60  # Proof object formula steps           : 21
% 0.42/0.60  # Proof object conjectures             : 21
% 0.42/0.60  # Proof object clause conjectures      : 18
% 0.42/0.60  # Proof object formula conjectures     : 3
% 0.42/0.60  # Proof object initial clauses used    : 13
% 0.42/0.60  # Proof object initial formulas used   : 10
% 0.42/0.60  # Proof object generating inferences   : 28
% 0.42/0.60  # Proof object simplifying inferences  : 29
% 0.42/0.60  # Training examples: 0 positive, 0 negative
% 0.42/0.60  # Parsed axioms                        : 10
% 0.42/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.60  # Initial clauses                      : 13
% 0.42/0.60  # Removed in clause preprocessing      : 0
% 0.42/0.60  # Initial clauses in saturation        : 13
% 0.42/0.60  # Processed clauses                    : 1668
% 0.42/0.60  # ...of these trivial                  : 372
% 0.42/0.60  # ...subsumed                          : 975
% 0.42/0.60  # ...remaining for further processing  : 321
% 0.42/0.60  # Other redundant clauses eliminated   : 0
% 0.42/0.60  # Clauses deleted for lack of memory   : 0
% 0.42/0.60  # Backward-subsumed                    : 7
% 0.42/0.60  # Backward-rewritten                   : 44
% 0.42/0.60  # Generated clauses                    : 21360
% 0.42/0.60  # ...of the previous two non-trivial   : 17547
% 0.42/0.60  # Contextual simplify-reflections      : 2
% 0.42/0.60  # Paramodulations                      : 21360
% 0.42/0.60  # Factorizations                       : 0
% 0.42/0.60  # Equation resolutions                 : 0
% 0.42/0.60  # Propositional unsat checks           : 0
% 0.42/0.60  #    Propositional check models        : 0
% 0.42/0.60  #    Propositional check unsatisfiable : 0
% 0.42/0.60  #    Propositional clauses             : 0
% 0.42/0.60  #    Propositional clauses after purity: 0
% 0.42/0.60  #    Propositional unsat core size     : 0
% 0.42/0.60  #    Propositional preprocessing time  : 0.000
% 0.42/0.60  #    Propositional encoding time       : 0.000
% 0.42/0.60  #    Propositional solver time         : 0.000
% 0.42/0.60  #    Success case prop preproc time    : 0.000
% 0.42/0.60  #    Success case prop encoding time   : 0.000
% 0.42/0.60  #    Success case prop solver time     : 0.000
% 0.42/0.60  # Current number of processed clauses  : 257
% 0.42/0.60  #    Positive orientable unit clauses  : 53
% 0.42/0.60  #    Positive unorientable unit clauses: 6
% 0.42/0.60  #    Negative unit clauses             : 3
% 0.42/0.60  #    Non-unit-clauses                  : 195
% 0.42/0.60  # Current number of unprocessed clauses: 15722
% 0.42/0.60  # ...number of literals in the above   : 55202
% 0.42/0.60  # Current number of archived formulas  : 0
% 0.42/0.60  # Current number of archived clauses   : 64
% 0.42/0.60  # Clause-clause subsumption calls (NU) : 7907
% 0.42/0.60  # Rec. Clause-clause subsumption calls : 5991
% 0.42/0.60  # Non-unit clause-clause subsumptions  : 806
% 0.42/0.60  # Unit Clause-clause subsumption calls : 750
% 0.42/0.60  # Rewrite failures with RHS unbound    : 0
% 0.42/0.60  # BW rewrite match attempts            : 393
% 0.42/0.60  # BW rewrite match successes           : 80
% 0.42/0.60  # Condensation attempts                : 0
% 0.42/0.60  # Condensation successes               : 0
% 0.42/0.60  # Termbank termtop insertions          : 399916
% 0.42/0.60  
% 0.42/0.60  # -------------------------------------------------
% 0.42/0.60  # User time                : 0.240 s
% 0.42/0.60  # System time              : 0.013 s
% 0.42/0.60  # Total time               : 0.253 s
% 0.42/0.60  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
