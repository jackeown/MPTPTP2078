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
% DateTime   : Thu Dec  3 10:54:56 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 385 expanded)
%              Number of clauses        :   42 ( 169 expanded)
%              Number of leaves         :    9 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 801 expanded)
%              Number of equality atoms :   54 ( 389 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    inference(assume_negation,[status(cth)],[t148_funct_1])).

fof(c_0_10,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) != k3_xboole_0(esk2_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_17,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) != k3_xboole_0(esk2_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k9_relat_1(X23,k1_relat_1(X23)) = k2_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | ~ r1_tarski(X26,k2_relat_1(X27))
      | k9_relat_1(X27,k10_relat_1(X27,X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k10_relat_1(X25,X24) = k10_relat_1(X25,k3_xboole_0(k2_relat_1(X25),X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_25,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) != k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_26,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_19])).

cnf(c_0_31,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))) != k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_34,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_18]),c_0_19])).

cnf(c_0_35,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2)))) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_18]),c_0_19])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))
    | r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),X2)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) != k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2)) = k9_relat_1(X1,k10_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X2,X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_18]),c_0_19])).

cnf(c_0_44,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_18]),c_0_19])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_18]),c_0_19])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))
    | r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),X2)
    | k9_relat_1(X1,k10_relat_1(X1,X2)) != k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))
    | r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),X1)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) != k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X4,X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_18]),c_0_19])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X3,X3,X3,X4))
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(esk3_0),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49]),c_0_27])]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))
    | r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k2_relat_1(X1))
    | k9_relat_1(X1,k10_relat_1(X1,X2)) != k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_42])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(esk3_0),k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk2_0)) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))
    | ~ r2_hidden(esk1_3(k2_relat_1(esk3_0),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(esk3_0),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k2_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_55]),c_0_49]),c_0_27])]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(esk3_0),k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk2_0)) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_59]),c_0_49]),c_0_27])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.71/0.88  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.71/0.88  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.71/0.88  #
% 0.71/0.88  # Preprocessing time       : 0.027 s
% 0.71/0.88  # Presaturation interreduction done
% 0.71/0.88  
% 0.71/0.88  # Proof found!
% 0.71/0.88  # SZS status Theorem
% 0.71/0.88  # SZS output start CNFRefutation
% 0.71/0.88  fof(t148_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 0.71/0.88  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.71/0.88  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.71/0.88  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.71/0.88  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.71/0.89  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.71/0.89  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.71/0.89  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.71/0.89  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.71/0.89  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))))), inference(assume_negation,[status(cth)],[t148_funct_1])).
% 0.71/0.89  fof(c_0_10, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.71/0.89  fof(c_0_11, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.71/0.89  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))!=k3_xboole_0(esk2_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.71/0.89  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.71/0.89  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.71/0.89  fof(c_0_15, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.71/0.89  fof(c_0_16, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.71/0.89  cnf(c_0_17, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))!=k3_xboole_0(esk2_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.71/0.89  cnf(c_0_18, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.71/0.89  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.71/0.89  fof(c_0_20, plain, ![X23]:(~v1_relat_1(X23)|k9_relat_1(X23,k1_relat_1(X23))=k2_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.71/0.89  fof(c_0_21, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.71/0.89  fof(c_0_22, plain, ![X26, X27]:(~v1_relat_1(X27)|~v1_funct_1(X27)|(~r1_tarski(X26,k2_relat_1(X27))|k9_relat_1(X27,k10_relat_1(X27,X26))=X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.71/0.89  cnf(c_0_23, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.71/0.89  fof(c_0_24, plain, ![X24, X25]:(~v1_relat_1(X25)|k10_relat_1(X25,X24)=k10_relat_1(X25,k3_xboole_0(k2_relat_1(X25),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.71/0.89  cnf(c_0_25, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))!=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_26, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.71/0.89  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.71/0.89  cnf(c_0_28, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.89  cnf(c_0_29, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.89  cnf(c_0_30, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_31, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.71/0.89  cnf(c_0_32, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.89  cnf(c_0_33, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))!=k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.71/0.89  cnf(c_0_34, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_35, plain, (k9_relat_1(X1,k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))))=k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.71/0.89  cnf(c_0_36, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.89  cnf(c_0_38, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.89  cnf(c_0_39, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.89  cnf(c_0_40, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))|r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),X2)|k1_setfam_1(k2_enumset1(X1,X1,X1,X2))!=k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.71/0.89  cnf(c_0_42, plain, (k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))=k9_relat_1(X1,k10_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.71/0.89  cnf(c_0_43, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X2,X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_44, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.89  cnf(c_0_46, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_47, plain, (r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.71/0.89  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))|r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),X2)|k9_relat_1(X1,k10_relat_1(X1,X2))!=k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.71/0.89  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.71/0.89  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(er,[status(thm)],[c_0_43])).
% 0.71/0.89  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))|r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),X1)|k1_setfam_1(k2_enumset1(X1,X1,X1,X2))!=k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_44])).
% 0.71/0.89  cnf(c_0_52, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X4,X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_18]), c_0_19])).
% 0.71/0.89  cnf(c_0_53, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X3,X3,X3,X4))|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X4)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.71/0.89  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(esk3_0),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_49]), c_0_27])]), c_0_50])).
% 0.71/0.89  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0))))|r2_hidden(esk1_3(k2_relat_1(X1),X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k2_relat_1(X1))|k9_relat_1(X1,k10_relat_1(X1,X2))!=k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_42])).
% 0.71/0.89  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_52])).
% 0.71/0.89  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k2_enumset1(k2_relat_1(esk3_0),k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk2_0))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))|~r2_hidden(esk1_3(k2_relat_1(esk3_0),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_54])])).
% 0.71/0.89  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(esk3_0),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))),k2_relat_1(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_55]), c_0_49]), c_0_27])]), c_0_56])).
% 0.71/0.89  cnf(c_0_59, negated_conjecture, (k1_setfam_1(k2_enumset1(k2_relat_1(esk3_0),k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk2_0))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k2_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.71/0.89  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_59]), c_0_49]), c_0_27])]), c_0_33]), ['proof']).
% 0.71/0.89  # SZS output end CNFRefutation
% 0.71/0.89  # Proof object total steps             : 61
% 0.71/0.89  # Proof object clause steps            : 42
% 0.71/0.89  # Proof object formula steps           : 19
% 0.71/0.89  # Proof object conjectures             : 17
% 0.71/0.89  # Proof object clause conjectures      : 14
% 0.71/0.89  # Proof object formula conjectures     : 3
% 0.71/0.89  # Proof object initial clauses used    : 16
% 0.71/0.89  # Proof object initial formulas used   : 9
% 0.71/0.89  # Proof object generating inferences   : 12
% 0.71/0.89  # Proof object simplifying inferences  : 40
% 0.71/0.89  # Training examples: 0 positive, 0 negative
% 0.71/0.89  # Parsed axioms                        : 9
% 0.71/0.89  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.89  # Initial clauses                      : 16
% 0.71/0.89  # Removed in clause preprocessing      : 3
% 0.71/0.89  # Initial clauses in saturation        : 13
% 0.71/0.89  # Processed clauses                    : 829
% 0.71/0.89  # ...of these trivial                  : 8
% 0.71/0.89  # ...subsumed                          : 385
% 0.71/0.89  # ...remaining for further processing  : 436
% 0.71/0.89  # Other redundant clauses eliminated   : 408
% 0.71/0.89  # Clauses deleted for lack of memory   : 0
% 0.71/0.89  # Backward-subsumed                    : 63
% 0.71/0.89  # Backward-rewritten                   : 63
% 0.71/0.89  # Generated clauses                    : 26799
% 0.71/0.89  # ...of the previous two non-trivial   : 25443
% 0.71/0.89  # Contextual simplify-reflections      : 15
% 0.71/0.89  # Paramodulations                      : 26255
% 0.71/0.89  # Factorizations                       : 134
% 0.71/0.89  # Equation resolutions                 : 410
% 0.71/0.89  # Propositional unsat checks           : 0
% 0.71/0.89  #    Propositional check models        : 0
% 0.71/0.89  #    Propositional check unsatisfiable : 0
% 0.71/0.89  #    Propositional clauses             : 0
% 0.71/0.89  #    Propositional clauses after purity: 0
% 0.71/0.89  #    Propositional unsat core size     : 0
% 0.71/0.89  #    Propositional preprocessing time  : 0.000
% 0.71/0.89  #    Propositional encoding time       : 0.000
% 0.71/0.89  #    Propositional solver time         : 0.000
% 0.71/0.89  #    Success case prop preproc time    : 0.000
% 0.71/0.89  #    Success case prop encoding time   : 0.000
% 0.71/0.89  #    Success case prop solver time     : 0.000
% 0.71/0.89  # Current number of processed clauses  : 294
% 0.71/0.89  #    Positive orientable unit clauses  : 20
% 0.71/0.89  #    Positive unorientable unit clauses: 0
% 0.71/0.89  #    Negative unit clauses             : 2
% 0.71/0.89  #    Non-unit-clauses                  : 272
% 0.71/0.89  # Current number of unprocessed clauses: 24206
% 0.71/0.89  # ...number of literals in the above   : 147157
% 0.71/0.89  # Current number of archived formulas  : 0
% 0.71/0.89  # Current number of archived clauses   : 142
% 0.71/0.89  # Clause-clause subsumption calls (NU) : 17266
% 0.71/0.89  # Rec. Clause-clause subsumption calls : 7046
% 0.71/0.89  # Non-unit clause-clause subsumptions  : 450
% 0.71/0.89  # Unit Clause-clause subsumption calls : 686
% 0.71/0.89  # Rewrite failures with RHS unbound    : 0
% 0.71/0.89  # BW rewrite match attempts            : 152
% 0.71/0.89  # BW rewrite match successes           : 22
% 0.71/0.89  # Condensation attempts                : 0
% 0.71/0.89  # Condensation successes               : 0
% 0.71/0.89  # Termbank termtop insertions          : 783227
% 0.71/0.89  
% 0.71/0.89  # -------------------------------------------------
% 0.71/0.89  # User time                : 0.534 s
% 0.71/0.89  # System time              : 0.011 s
% 0.71/0.89  # Total time               : 0.545 s
% 0.71/0.89  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
