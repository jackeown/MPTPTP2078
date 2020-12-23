%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 185 expanded)
%              Number of clauses        :   32 (  75 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 287 expanded)
%              Number of equality atoms :   29 ( 129 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t158_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)) ) ),
    inference(assume_negation,[status(cth)],[t149_funct_1])).

fof(c_0_16,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | r1_tarski(X9,k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k1_setfam_1(k3_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_20]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_34,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_35,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X38)
      | k10_relat_1(k7_relat_1(X38,X36),X37) = k3_xboole_0(X36,k10_relat_1(X38,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k1_setfam_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_26]),c_0_27])).

fof(c_0_38,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_relat_1(X30)
      | ~ r1_tarski(X29,X30)
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k9_relat_1(X29,X27),k9_relat_1(X30,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k9_relat_1(esk3_0,esk1_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | r1_tarski(k9_relat_1(X40,k10_relat_1(X40,X39)),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_48,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(X32,X33)
      | k9_relat_1(k7_relat_1(X31,X33),X32) = k9_relat_1(X31,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_49,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_25]),c_0_26]),c_0_27])).

fof(c_0_50,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | v1_relat_1(k7_relat_1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_52,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_49])).

cnf(c_0_55,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_49]),c_0_44])])).

cnf(c_0_57,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(k7_relat_1(X1,X2),X3)),X3)
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])).

fof(c_0_58,plain,(
    ! [X34,X35] :
      ( ( v1_relat_1(k7_relat_1(X34,X35))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( v1_funct_1(k7_relat_1(X34,X35))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_44])])).

cnf(c_0_60,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:08:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t149_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 0.20/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.38  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.20/0.38  fof(t158_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.20/0.38  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.38  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.20/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.38  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.20/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t149_funct_1])).
% 0.20/0.38  fof(c_0_16, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.38  fof(c_0_17, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.38  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_21, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_22, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_tarski(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  fof(c_0_29, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|r1_tarski(X9,k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k1_setfam_1(k3_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.20/0.38  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_20]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.20/0.38  cnf(c_0_32, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  fof(c_0_33, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.38  fof(c_0_34, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  fof(c_0_35, plain, ![X36, X37, X38]:(~v1_relat_1(X38)|k10_relat_1(k7_relat_1(X38,X36),X37)=k3_xboole_0(X36,k10_relat_1(X38,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k1_setfam_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0))))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.38  cnf(c_0_37, plain, (r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_26]), c_0_27])).
% 0.20/0.38  fof(c_0_38, plain, ![X27, X28, X29, X30]:(~v1_relat_1(X29)|(~v1_relat_1(X30)|(~r1_tarski(X29,X30)|~r1_tarski(X27,X28)|r1_tarski(k9_relat_1(X29,X27),k9_relat_1(X30,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).
% 0.20/0.38  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_41, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k9_relat_1(esk3_0,esk1_0))|~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_43, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_45, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_25]), c_0_26]), c_0_27])).
% 0.20/0.38  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.38  fof(c_0_47, plain, ![X39, X40]:(~v1_relat_1(X40)|~v1_funct_1(X40)|r1_tarski(k9_relat_1(X40,k10_relat_1(X40,X39)),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.38  fof(c_0_48, plain, ![X31, X32, X33]:(~v1_relat_1(X31)|(~r1_tarski(X32,X33)|k9_relat_1(k7_relat_1(X31,X33),X32)=k9_relat_1(X31,X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.20/0.38  cnf(c_0_49, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_25]), c_0_26]), c_0_27])).
% 0.20/0.38  fof(c_0_50, plain, ![X25, X26]:(~v1_relat_1(X25)|v1_relat_1(k7_relat_1(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46])])).
% 0.20/0.38  cnf(c_0_52, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_53, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_54, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_49])).
% 0.20/0.38  cnf(c_0_55, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_49]), c_0_44])])).
% 0.20/0.38  cnf(c_0_57, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(k7_relat_1(X1,X2),X3)),X3)|~v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])).
% 0.20/0.38  fof(c_0_58, plain, ![X34, X35]:((v1_relat_1(k7_relat_1(X34,X35))|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(v1_funct_1(k7_relat_1(X34,X35))|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (~v1_funct_1(k7_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_44])])).
% 0.20/0.38  cnf(c_0_60, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_44])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 63
% 0.20/0.38  # Proof object clause steps            : 32
% 0.20/0.38  # Proof object formula steps           : 31
% 0.20/0.38  # Proof object conjectures             : 13
% 0.20/0.38  # Proof object clause conjectures      : 10
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 15
% 0.20/0.38  # Proof object generating inferences   : 7
% 0.20/0.38  # Proof object simplifying inferences  : 37
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 15
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 20
% 0.20/0.38  # Removed in clause preprocessing      : 4
% 0.20/0.38  # Initial clauses in saturation        : 16
% 0.20/0.38  # Processed clauses                    : 63
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 13
% 0.20/0.38  # ...remaining for further processing  : 49
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 71
% 0.20/0.38  # ...of the previous two non-trivial   : 62
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 69
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 32
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 6
% 0.20/0.39  #    Non-unit-clauses                  : 20
% 0.20/0.39  # Current number of unprocessed clauses: 29
% 0.20/0.39  # ...number of literals in the above   : 95
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 19
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 58
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 44
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 10
% 0.20/0.39  # Unit Clause-clause subsumption calls : 24
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 18
% 0.20/0.39  # BW rewrite match successes           : 16
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 2158
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.031 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.036 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
