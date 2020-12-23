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
% DateTime   : Thu Dec  3 10:54:54 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 564 expanded)
%              Number of clauses        :   73 ( 255 expanded)
%              Number of leaves         :   12 ( 139 expanded)
%              Depth                    :   21
%              Number of atoms          :  301 (1719 expanded)
%              Number of equality atoms :   92 ( 618 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t148_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(t137_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_12,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    inference(assume_negation,[status(cth)],[t148_funct_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33] :
      ( ( r2_hidden(X30,k1_relat_1(X27))
        | ~ r2_hidden(X30,X29)
        | X29 != k10_relat_1(X27,X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(k1_funct_1(X27,X30),X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k10_relat_1(X27,X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(X31,k1_relat_1(X27))
        | ~ r2_hidden(k1_funct_1(X27,X31),X28)
        | r2_hidden(X31,X29)
        | X29 != k10_relat_1(X27,X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(esk2_3(X27,X32,X33),X33)
        | ~ r2_hidden(esk2_3(X27,X32,X33),k1_relat_1(X27))
        | ~ r2_hidden(k1_funct_1(X27,esk2_3(X27,X32,X33)),X32)
        | X33 = k10_relat_1(X27,X32)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(esk2_3(X27,X32,X33),k1_relat_1(X27))
        | r2_hidden(esk2_3(X27,X32,X33),X33)
        | X33 = k10_relat_1(X27,X32)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(k1_funct_1(X27,esk2_3(X27,X32,X33)),X32)
        | r2_hidden(esk2_3(X27,X32,X33),X33)
        | X33 = k10_relat_1(X27,X32)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)) != k3_xboole_0(esk3_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k10_relat_1(esk4_0,X2)
    | r2_hidden(esk2_3(esk4_0,X2,X1),k1_relat_1(esk4_0))
    | r2_hidden(esk2_3(esk4_0,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

fof(c_0_33,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | k10_relat_1(X37,k3_xboole_0(X35,X36)) = k3_xboole_0(k10_relat_1(X37,X35),k10_relat_1(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).

cnf(c_0_34,plain,
    ( X3 = k10_relat_1(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,esk2_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X1),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk4_0) = k10_relat_1(esk4_0,X1)
    | r2_hidden(esk2_3(esk4_0,X1,k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) ),
    inference(ef,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k10_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k10_relat_1(X26,k2_relat_1(X26)) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_41,plain,
    ( X1 = k10_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk2_3(X2,X3,X1),k10_relat_1(X2,X3))
    | ~ r2_hidden(esk2_3(X2,X3,X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(esk4_0) = k10_relat_1(esk4_0,X1)
    | r2_hidden(esk1_3(k1_relat_1(esk4_0),X2,k1_relat_1(esk4_0)),k1_relat_1(esk4_0))
    | r2_hidden(esk2_3(esk4_0,X1,k1_relat_1(esk4_0)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k10_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_19]),c_0_19])).

cnf(c_0_44,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk4_0) = k10_relat_1(esk4_0,X1)
    | r2_hidden(esk1_3(k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26]),c_0_27])]),c_0_38])).

cnf(c_0_46,plain,
    ( k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X2))) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k10_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_48,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | r1_tarski(k3_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

fof(c_0_49,plain,(
    ! [X19,X20] : k2_tarski(X19,X20) = k2_tarski(X20,X19) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_50,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1))) = k1_relat_1(esk4_0)
    | r2_hidden(esk1_3(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1))),k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26]),c_0_27])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_47,c_0_19])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))) = k1_relat_1(esk4_0)
    | r2_hidden(esk1_3(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))),k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_27])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k1_enumset1(X2,X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_19])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_19])).

cnf(c_0_61,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_16]),c_0_16])).

cnf(c_0_62,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))))) = k1_relat_1(esk4_0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))) = k1_relat_1(esk4_0)
    | ~ r2_hidden(esk1_3(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))),k1_relat_1(esk4_0)),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_59])).

fof(c_0_64,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))))) = k1_relat_1(esk4_0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))) = k1_relat_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_31])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,k1_setfam_1(k1_enumset1(X3,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))) = k1_relat_1(esk4_0)
    | r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k10_relat_1(X2,k2_relat_1(X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X2),k1_relat_1(X2),k10_relat_1(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_46])).

cnf(c_0_73,plain,
    ( X1 = k1_setfam_1(k1_enumset1(X2,X2,X3))
    | ~ r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))) = k1_relat_1(esk4_0)
    | r1_tarski(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

fof(c_0_75,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ r1_tarski(X38,k2_relat_1(X39))
      | k9_relat_1(X39,k10_relat_1(X39,X38)) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_76,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),X3)) = k10_relat_1(X1,X2)
    | r2_hidden(esk1_3(k10_relat_1(X1,X2),X3,k10_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k10_relat_1(X2,k2_relat_1(X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X2),k1_relat_1(X2),k1_relat_1(X2)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_44])).

cnf(c_0_78,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_71])])).

cnf(c_0_79,negated_conjecture,
    ( k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)) != k3_xboole_0(esk3_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_80,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | k9_relat_1(X25,k1_relat_1(X25)) = k2_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_81,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k1_relat_1(X1))) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,k2_relat_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_83,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X1),X2)) = k10_relat_1(esk4_0,X1)
    | r2_hidden(esk1_3(k10_relat_1(esk4_0,X1),X2,k10_relat_1(esk4_0,X1)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_26]),c_0_27])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk4_0,k2_relat_1(esk4_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_26]),c_0_27])])).

cnf(c_0_85,negated_conjecture,
    ( k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)) != k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_19])).

cnf(c_0_86,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))) = k1_setfam_1(k1_enumset1(X2,X2,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X3,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_65])).

cnf(c_0_88,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(esk4_0)))) = k10_relat_1(esk4_0,X1)
    | r2_hidden(esk1_3(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_26]),c_0_27])])).

cnf(c_0_89,negated_conjecture,
    ( X1 = k10_relat_1(esk4_0,k2_relat_1(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_relat_1(esk4_0),X1),k1_relat_1(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_relat_1(esk4_0),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_84]),c_0_26]),c_0_27])])).

cnf(c_0_90,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k2_relat_1(esk4_0))) != k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_27])])).

cnf(c_0_91,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(esk4_0))) = k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))
    | r2_hidden(esk1_3(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_26]),c_0_27]),c_0_71])])).

cnf(c_0_92,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_relat_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_38]),c_0_38])).

cnf(c_0_93,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_31])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk1_3(k10_relat_1(esk4_0,esk3_0),k1_relat_1(esk4_0),k10_relat_1(esk4_0,esk3_0)),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0))) = k10_relat_1(esk4_0,k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_92]),c_0_26]),c_0_27])])).

cnf(c_0_96,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k2_relat_1(esk4_0)))) = k10_relat_1(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_96]),c_0_26]),c_0_27]),c_0_71])]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.06/2.26  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.06/2.26  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.06/2.26  #
% 2.06/2.26  # Preprocessing time       : 0.028 s
% 2.06/2.26  # Presaturation interreduction done
% 2.06/2.26  
% 2.06/2.26  # Proof found!
% 2.06/2.26  # SZS status Theorem
% 2.06/2.26  # SZS output start CNFRefutation
% 2.06/2.26  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.06/2.26  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/2.26  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.06/2.26  fof(t148_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 2.06/2.26  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 2.06/2.26  fof(t137_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 2.06/2.26  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.06/2.26  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.06/2.26  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.06/2.26  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/2.26  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.06/2.26  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.06/2.26  fof(c_0_12, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.06/2.26  fof(c_0_13, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.06/2.26  fof(c_0_14, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 2.06/2.26  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.06/2.26  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.06/2.26  fof(c_0_17, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))))), inference(assume_negation,[status(cth)],[t148_funct_1])).
% 2.06/2.26  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.26  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 2.06/2.26  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.26  fof(c_0_21, plain, ![X27, X28, X29, X30, X31, X32, X33]:((((r2_hidden(X30,k1_relat_1(X27))|~r2_hidden(X30,X29)|X29!=k10_relat_1(X27,X28)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(r2_hidden(k1_funct_1(X27,X30),X28)|~r2_hidden(X30,X29)|X29!=k10_relat_1(X27,X28)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(~r2_hidden(X31,k1_relat_1(X27))|~r2_hidden(k1_funct_1(X27,X31),X28)|r2_hidden(X31,X29)|X29!=k10_relat_1(X27,X28)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&((~r2_hidden(esk2_3(X27,X32,X33),X33)|(~r2_hidden(esk2_3(X27,X32,X33),k1_relat_1(X27))|~r2_hidden(k1_funct_1(X27,esk2_3(X27,X32,X33)),X32))|X33=k10_relat_1(X27,X32)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&((r2_hidden(esk2_3(X27,X32,X33),k1_relat_1(X27))|r2_hidden(esk2_3(X27,X32,X33),X33)|X33=k10_relat_1(X27,X32)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(r2_hidden(k1_funct_1(X27,esk2_3(X27,X32,X33)),X32)|r2_hidden(esk2_3(X27,X32,X33),X33)|X33=k10_relat_1(X27,X32)|(~v1_relat_1(X27)|~v1_funct_1(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 2.06/2.26  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0))!=k3_xboole_0(esk3_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 2.06/2.26  cnf(c_0_23, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 2.06/2.26  cnf(c_0_24, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 2.06/2.26  cnf(c_0_25, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.06/2.26  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.06/2.26  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.06/2.26  cnf(c_0_28, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,X4)|X4!=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.06/2.26  cnf(c_0_29, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.06/2.26  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X3,X3,X2)))), inference(er,[status(thm)],[c_0_23])).
% 2.06/2.26  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_24])).
% 2.06/2.26  cnf(c_0_32, negated_conjecture, (X1=k10_relat_1(esk4_0,X2)|r2_hidden(esk2_3(esk4_0,X2,X1),k1_relat_1(esk4_0))|r2_hidden(esk2_3(esk4_0,X2,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 2.06/2.26  fof(c_0_33, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|~v1_funct_1(X37)|k10_relat_1(X37,k3_xboole_0(X35,X36))=k3_xboole_0(k10_relat_1(X37,X35),k10_relat_1(X37,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).
% 2.06/2.26  cnf(c_0_34, plain, (X3=k10_relat_1(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(k1_funct_1(X1,esk2_3(X1,X2,X3)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.06/2.26  cnf(c_0_35, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))), inference(er,[status(thm)],[c_0_28])).
% 2.06/2.26  cnf(c_0_36, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_29])).
% 2.06/2.26  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X1),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.06/2.26  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk4_0)=k10_relat_1(esk4_0,X1)|r2_hidden(esk2_3(esk4_0,X1,k1_relat_1(esk4_0)),k1_relat_1(esk4_0))), inference(ef,[status(thm)],[c_0_32])).
% 2.06/2.26  cnf(c_0_39, plain, (k10_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.06/2.26  fof(c_0_40, plain, ![X26]:(~v1_relat_1(X26)|k10_relat_1(X26,k2_relat_1(X26))=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 2.06/2.26  cnf(c_0_41, plain, (X1=k10_relat_1(X2,X3)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(esk2_3(X2,X3,X1),k10_relat_1(X2,X3))|~r2_hidden(esk2_3(X2,X3,X1),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 2.06/2.26  cnf(c_0_42, negated_conjecture, (k1_relat_1(esk4_0)=k10_relat_1(esk4_0,X1)|r2_hidden(esk1_3(k1_relat_1(esk4_0),X2,k1_relat_1(esk4_0)),k1_relat_1(esk4_0))|r2_hidden(esk2_3(esk4_0,X1,k1_relat_1(esk4_0)),X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.06/2.26  cnf(c_0_43, plain, (k10_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))=k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_19]), c_0_19])).
% 2.06/2.26  cnf(c_0_44, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.06/2.26  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk4_0)=k10_relat_1(esk4_0,X1)|r2_hidden(esk1_3(k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0)),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_26]), c_0_27])]), c_0_38])).
% 2.06/2.26  cnf(c_0_46, plain, (k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X2)))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k10_relat_1(X1,X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.06/2.26  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.26  fof(c_0_48, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|r1_tarski(k3_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 2.06/2.26  fof(c_0_49, plain, ![X19, X20]:k2_tarski(X19,X20)=k2_tarski(X20,X19), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 2.06/2.26  cnf(c_0_50, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.26  cnf(c_0_51, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1)))=k1_relat_1(esk4_0)|r2_hidden(esk1_3(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1))),k1_relat_1(esk4_0)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26]), c_0_27])])).
% 2.06/2.26  cnf(c_0_52, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_47, c_0_19])).
% 2.06/2.26  cnf(c_0_53, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.26  cnf(c_0_54, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.06/2.26  cnf(c_0_55, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.06/2.26  cnf(c_0_56, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_50, c_0_19])).
% 2.06/2.26  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)|r2_hidden(esk1_3(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))),k1_relat_1(esk4_0)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_27])])).
% 2.06/2.26  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(er,[status(thm)],[c_0_52])).
% 2.06/2.26  cnf(c_0_59, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k1_enumset1(X2,X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_19])).
% 2.06/2.26  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_19])).
% 2.06/2.26  cnf(c_0_61, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_16]), c_0_16])).
% 2.06/2.26  cnf(c_0_62, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))))=k1_relat_1(esk4_0)|k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)|~r2_hidden(esk1_3(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))),k1_relat_1(esk4_0)),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 2.06/2.26  cnf(c_0_63, plain, (r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_59])).
% 2.06/2.26  fof(c_0_64, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.06/2.26  cnf(c_0_65, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 2.06/2.26  cnf(c_0_66, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))))=k1_relat_1(esk4_0)|k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_31])).
% 2.06/2.26  cnf(c_0_67, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.06/2.26  cnf(c_0_68, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,k1_setfam_1(k1_enumset1(X3,X3,X4))))), inference(spm,[status(thm)],[c_0_58, c_0_43])).
% 2.06/2.26  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.06/2.26  cnf(c_0_70, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)|r1_tarski(k1_relat_1(esk4_0),X1)|~r1_tarski(k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.06/2.26  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_67])).
% 2.06/2.26  cnf(c_0_72, plain, (r2_hidden(X1,k10_relat_1(X2,k2_relat_1(X2)))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X2),k1_relat_1(X2),k10_relat_1(X2,X3))))), inference(spm,[status(thm)],[c_0_68, c_0_46])).
% 2.06/2.26  cnf(c_0_73, plain, (X1=k1_setfam_1(k1_enumset1(X2,X2,X3))|~r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_60])).
% 2.06/2.26  cnf(c_0_74, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)|r1_tarski(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.06/2.26  fof(c_0_75, plain, ![X38, X39]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~r1_tarski(X38,k2_relat_1(X39))|k9_relat_1(X39,k10_relat_1(X39,X38))=X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 2.06/2.26  cnf(c_0_76, plain, (k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),X3))=k10_relat_1(X1,X2)|r2_hidden(esk1_3(k10_relat_1(X1,X2),X3,k10_relat_1(X1,X2)),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 2.06/2.26  cnf(c_0_77, plain, (r2_hidden(X1,k10_relat_1(X2,k2_relat_1(X2)))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X2),k1_relat_1(X2),k1_relat_1(X2))))), inference(spm,[status(thm)],[c_0_72, c_0_44])).
% 2.06/2.26  cnf(c_0_78, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_71])])).
% 2.06/2.26  cnf(c_0_79, negated_conjecture, (k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0))!=k3_xboole_0(esk3_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.06/2.26  fof(c_0_80, plain, ![X25]:(~v1_relat_1(X25)|k9_relat_1(X25,k1_relat_1(X25))=k2_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 2.06/2.26  cnf(c_0_81, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 2.06/2.26  cnf(c_0_82, plain, (k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k1_relat_1(X1)))=k10_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,k2_relat_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.06/2.26  cnf(c_0_83, negated_conjecture, (k1_setfam_1(k1_enumset1(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X1),X2))=k10_relat_1(esk4_0,X1)|r2_hidden(esk1_3(k10_relat_1(esk4_0,X1),X2,k10_relat_1(esk4_0,X1)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_26]), c_0_27])])).
% 2.06/2.26  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk4_0,k2_relat_1(esk4_0)))|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_26]), c_0_27])])).
% 2.06/2.26  cnf(c_0_85, negated_conjecture, (k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0))!=k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0))))), inference(rw,[status(thm)],[c_0_79, c_0_19])).
% 2.06/2.26  cnf(c_0_86, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 2.06/2.26  cnf(c_0_87, plain, (k9_relat_1(X1,k10_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))))=k1_setfam_1(k1_enumset1(X2,X2,X3))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X3,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_81, c_0_65])).
% 2.06/2.26  cnf(c_0_88, negated_conjecture, (k10_relat_1(esk4_0,k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(esk4_0))))=k10_relat_1(esk4_0,X1)|r2_hidden(esk1_3(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_26]), c_0_27])])).
% 2.06/2.26  cnf(c_0_89, negated_conjecture, (X1=k10_relat_1(esk4_0,k2_relat_1(esk4_0))|~r2_hidden(esk2_3(esk4_0,k2_relat_1(esk4_0),X1),k1_relat_1(esk4_0))|~r2_hidden(esk2_3(esk4_0,k2_relat_1(esk4_0),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_84]), c_0_26]), c_0_27])])).
% 2.06/2.26  cnf(c_0_90, negated_conjecture, (k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k2_relat_1(esk4_0)))!=k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_27])])).
% 2.06/2.26  cnf(c_0_91, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(esk4_0)))=k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))|r2_hidden(esk1_3(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0),k10_relat_1(esk4_0,X1)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_26]), c_0_27]), c_0_71])])).
% 2.06/2.26  cnf(c_0_92, negated_conjecture, (k10_relat_1(esk4_0,k2_relat_1(esk4_0))=k1_relat_1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_38]), c_0_38])).
% 2.06/2.26  cnf(c_0_93, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_31])).
% 2.06/2.26  cnf(c_0_94, negated_conjecture, (r2_hidden(esk1_3(k10_relat_1(esk4_0,esk3_0),k1_relat_1(esk4_0),k10_relat_1(esk4_0,esk3_0)),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 2.06/2.26  cnf(c_0_95, negated_conjecture, (k1_setfam_1(k1_enumset1(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0)))=k10_relat_1(esk4_0,k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_92]), c_0_26]), c_0_27])])).
% 2.06/2.26  cnf(c_0_96, negated_conjecture, (k10_relat_1(esk4_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k2_relat_1(esk4_0))))=k10_relat_1(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 2.06/2.26  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_96]), c_0_26]), c_0_27]), c_0_71])]), c_0_90]), ['proof']).
% 2.06/2.26  # SZS output end CNFRefutation
% 2.06/2.26  # Proof object total steps             : 98
% 2.06/2.26  # Proof object clause steps            : 73
% 2.06/2.26  # Proof object formula steps           : 25
% 2.06/2.26  # Proof object conjectures             : 29
% 2.06/2.26  # Proof object clause conjectures      : 26
% 2.06/2.26  # Proof object formula conjectures     : 3
% 2.06/2.26  # Proof object initial clauses used    : 22
% 2.06/2.26  # Proof object initial formulas used   : 12
% 2.06/2.26  # Proof object generating inferences   : 35
% 2.06/2.26  # Proof object simplifying inferences  : 62
% 2.06/2.26  # Training examples: 0 positive, 0 negative
% 2.06/2.26  # Parsed axioms                        : 12
% 2.06/2.26  # Removed by relevancy pruning/SinE    : 0
% 2.06/2.26  # Initial clauses                      : 26
% 2.06/2.26  # Removed in clause preprocessing      : 2
% 2.06/2.26  # Initial clauses in saturation        : 24
% 2.06/2.26  # Processed clauses                    : 4079
% 2.06/2.26  # ...of these trivial                  : 55
% 2.06/2.26  # ...subsumed                          : 2829
% 2.06/2.26  # ...remaining for further processing  : 1195
% 2.06/2.26  # Other redundant clauses eliminated   : 6950
% 2.06/2.26  # Clauses deleted for lack of memory   : 0
% 2.06/2.26  # Backward-subsumed                    : 27
% 2.06/2.26  # Backward-rewritten                   : 79
% 2.06/2.26  # Generated clauses                    : 119329
% 2.06/2.26  # ...of the previous two non-trivial   : 110535
% 2.06/2.26  # Contextual simplify-reflections      : 19
% 2.06/2.26  # Paramodulations                      : 112175
% 2.06/2.26  # Factorizations                       : 204
% 2.06/2.26  # Equation resolutions                 : 6950
% 2.06/2.26  # Propositional unsat checks           : 0
% 2.06/2.26  #    Propositional check models        : 0
% 2.06/2.26  #    Propositional check unsatisfiable : 0
% 2.06/2.26  #    Propositional clauses             : 0
% 2.06/2.26  #    Propositional clauses after purity: 0
% 2.06/2.26  #    Propositional unsat core size     : 0
% 2.06/2.26  #    Propositional preprocessing time  : 0.000
% 2.06/2.26  #    Propositional encoding time       : 0.000
% 2.06/2.26  #    Propositional solver time         : 0.000
% 2.06/2.26  #    Success case prop preproc time    : 0.000
% 2.06/2.26  #    Success case prop encoding time   : 0.000
% 2.06/2.26  #    Success case prop solver time     : 0.000
% 2.06/2.26  # Current number of processed clauses  : 1058
% 2.06/2.26  #    Positive orientable unit clauses  : 26
% 2.06/2.26  #    Positive unorientable unit clauses: 2
% 2.06/2.26  #    Negative unit clauses             : 1
% 2.06/2.26  #    Non-unit-clauses                  : 1029
% 2.06/2.26  # Current number of unprocessed clauses: 105950
% 2.06/2.26  # ...number of literals in the above   : 672320
% 2.06/2.26  # Current number of archived formulas  : 0
% 2.06/2.26  # Current number of archived clauses   : 131
% 2.06/2.26  # Clause-clause subsumption calls (NU) : 323709
% 2.06/2.26  # Rec. Clause-clause subsumption calls : 79010
% 2.06/2.26  # Non-unit clause-clause subsumptions  : 2863
% 2.06/2.26  # Unit Clause-clause subsumption calls : 2473
% 2.06/2.26  # Rewrite failures with RHS unbound    : 0
% 2.06/2.26  # BW rewrite match attempts            : 351
% 2.06/2.26  # BW rewrite match successes           : 24
% 2.06/2.26  # Condensation attempts                : 0
% 2.06/2.26  # Condensation successes               : 0
% 2.06/2.26  # Termbank termtop insertions          : 4510376
% 2.06/2.26  
% 2.06/2.26  # -------------------------------------------------
% 2.06/2.26  # User time                : 1.858 s
% 2.06/2.26  # System time              : 0.056 s
% 2.06/2.26  # Total time               : 1.914 s
% 2.06/2.26  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
