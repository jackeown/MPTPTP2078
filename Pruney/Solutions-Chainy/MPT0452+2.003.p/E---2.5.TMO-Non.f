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
% DateTime   : Thu Dec  3 10:48:35 EST 2020

% Result     : Timeout 58.15s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   84 (47274 expanded)
%              Number of clauses        :   67 (21789 expanded)
%              Number of leaves         :    8 (12230 expanded)
%              Depth                    :   26
%              Number of atoms          :  237 (117424 expanded)
%              Number of equality atoms :   62 (53017 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t38_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k3_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).

fof(c_0_8,plain,(
    ! [X19,X20] : k3_tarski(k2_tarski(X19,X20)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k3_relat_1(X21) = k2_xboole_0(k1_relat_1(X21),k2_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_11,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_15,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X23] :
      ( ( k2_relat_1(X23) = k1_relat_1(k4_relat_1(X23))
        | ~ v1_relat_1(X23) )
      & ( k1_relat_1(X23) = k2_relat_1(k4_relat_1(X23))
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_19,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k4_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k3_relat_1(X1) = k3_relat_1(k4_relat_1(X1)) ) ),
    inference(assume_negation,[status(cth)],[t38_relat_1])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_24,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k3_relat_1(esk2_0) != k3_relat_1(k4_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_27,plain,
    ( X3 = k3_tarski(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_16]),c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k2_enumset1(X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_16]),c_0_17])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(X1)),k1_relat_1(k4_relat_1(X1)),k1_relat_1(k4_relat_1(X1)),k1_relat_1(X1))) = k3_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( k3_relat_1(esk2_0) != k3_relat_1(k4_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_hidden(esk1_3(X3,X4,X2),X3)
    | r2_hidden(esk1_3(X3,X4,X2),X4)
    | r2_hidden(esk1_3(X3,X4,X2),X2)
    | r2_hidden(esk1_3(X3,X4,X1),X3)
    | r2_hidden(esk1_3(X3,X4,X1),X4)
    | r2_hidden(esk1_3(X3,X4,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_enumset1(X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_16]),c_0_17])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k3_tarski(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k1_relat_1(X1))) = k3_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(k4_relat_1(esk2_0)))
    | r2_hidden(esk1_3(X1,X2,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X2,k3_relat_1(k4_relat_1(esk2_0))),X2)
    | r2_hidden(esk1_3(X1,X2,k3_relat_1(k4_relat_1(esk2_0))),X1)
    | r2_hidden(esk1_3(X1,X2,k3_relat_1(esk2_0)),X2)
    | r2_hidden(esk1_3(X1,X2,k3_relat_1(esk2_0)),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_enumset1(X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_16]),c_0_17])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k3_relat_1(k4_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(k4_relat_1(esk2_0)))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),X1)
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( X1 = k3_tarski(k2_enumset1(X2,X2,X2,X2))
    | r2_hidden(esk1_3(X2,X2,X1),X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k2_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),X1)
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_3(X1,X1,X2),X2)
    | r2_hidden(esk1_3(X1,X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_44])).

cnf(c_0_49,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43])]),c_0_48])).

cnf(c_0_52,plain,
    ( X3 = k3_tarski(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_16]),c_0_17])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_25])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k3_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43])])).

cnf(c_0_56,plain,
    ( k3_relat_1(k4_relat_1(X1)) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),k2_relat_1(X1))
    | ~ r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k2_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_43])])).

cnf(c_0_58,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X1)) = k3_relat_1(k4_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1)
    | ~ r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_43])])).

cnf(c_0_60,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_58]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k3_tarski(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0))) = k3_relat_1(k4_relat_1(esk2_0))
    | r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))
    | r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_55])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k3_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))
    | r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_32])).

cnf(c_0_64,plain,
    ( k3_relat_1(k4_relat_1(X1)) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),k1_relat_1(X1))
    | ~ r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_63]),c_0_43])])).

cnf(c_0_66,negated_conjecture,
    ( k3_tarski(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0))) = k3_relat_1(k4_relat_1(esk2_0))
    | r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_63]),c_0_43])]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_66]),c_0_32])).

cnf(c_0_68,plain,
    ( X1 = k3_tarski(k2_enumset1(X2,X2,X2,k1_relat_1(X3)))
    | r2_hidden(esk1_3(X2,k1_relat_1(X3),X1),k3_relat_1(X3))
    | r2_hidden(esk1_3(X2,k1_relat_1(X3),X1),X2)
    | r2_hidden(esk1_3(X2,k1_relat_1(X3),X1),X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( k3_tarski(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0))) = k3_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_67]),c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( X1 = k3_tarski(k2_enumset1(X2,X2,X2,k1_relat_1(esk2_0)))
    | r2_hidden(esk1_3(X2,k1_relat_1(esk2_0),X1),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X2,k1_relat_1(esk2_0),X1),X1)
    | r2_hidden(esk1_3(X2,k1_relat_1(esk2_0),X1),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_43])).

cnf(c_0_71,negated_conjecture,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k1_relat_1(esk2_0))) = k3_relat_1(esk2_0)
    | r2_hidden(esk1_3(X1,k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | r2_hidden(esk1_3(X1,k1_relat_1(esk2_0),k3_relat_1(esk2_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_69]),c_0_69]),c_0_69]),c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k2_relat_1(esk2_0))
    | r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_71]),c_0_43])]),c_0_32])).

cnf(c_0_73,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_72]),c_0_43])])).

cnf(c_0_75,plain,
    ( X3 = k3_tarski(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_16]),c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( k3_tarski(k2_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k1_relat_1(esk2_0))) = k3_relat_1(esk2_0)
    | ~ r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_74])).

cnf(c_0_77,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X3,X3,X3,X4))
    | ~ r2_hidden(esk1_3(X3,X4,k3_tarski(k2_enumset1(X1,X1,X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k3_tarski(k2_enumset1(X1,X1,X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_40])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k1_relat_1(esk2_0))
    | r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_74]),c_0_43])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k1_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_76]),c_0_43])]),c_0_32])).

cnf(c_0_80,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk1_3(X2,X3,k3_relat_1(X1)),k2_relat_1(X1))
    | ~ r2_hidden(esk1_3(X2,X3,k3_relat_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k2_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( k3_tarski(k2_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k1_relat_1(esk2_0))) = k3_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_43]),c_0_81])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_82]),c_0_43])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 58.15/58.33  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 58.15/58.33  # and selection function SelectComplexExceptUniqMaxHorn.
% 58.15/58.33  #
% 58.15/58.33  # Preprocessing time       : 0.026 s
% 58.15/58.33  # Presaturation interreduction done
% 58.15/58.33  
% 58.15/58.33  # Proof found!
% 58.15/58.33  # SZS status Theorem
% 58.15/58.33  # SZS output start CNFRefutation
% 58.15/58.33  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 58.15/58.33  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 58.15/58.33  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 58.15/58.33  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 58.15/58.33  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 58.15/58.33  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 58.15/58.33  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 58.15/58.33  fof(t38_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k3_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relat_1)).
% 58.15/58.33  fof(c_0_8, plain, ![X19, X20]:k3_tarski(k2_tarski(X19,X20))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 58.15/58.33  fof(c_0_9, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 58.15/58.33  fof(c_0_10, plain, ![X21]:(~v1_relat_1(X21)|k3_relat_1(X21)=k2_xboole_0(k1_relat_1(X21),k2_relat_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 58.15/58.33  cnf(c_0_11, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 58.15/58.33  cnf(c_0_12, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 58.15/58.33  fof(c_0_13, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 58.15/58.33  fof(c_0_14, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 58.15/58.33  cnf(c_0_15, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 58.15/58.33  cnf(c_0_16, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 58.15/58.33  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 58.15/58.33  fof(c_0_18, plain, ![X23]:((k2_relat_1(X23)=k1_relat_1(k4_relat_1(X23))|~v1_relat_1(X23))&(k1_relat_1(X23)=k2_relat_1(k4_relat_1(X23))|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 58.15/58.33  fof(c_0_19, plain, ![X22]:(~v1_relat_1(X22)|v1_relat_1(k4_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 58.15/58.33  fof(c_0_20, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k3_relat_1(k4_relat_1(X1)))), inference(assume_negation,[status(cth)],[t38_relat_1])).
% 58.15/58.33  cnf(c_0_21, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.15/58.33  cnf(c_0_22, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.15/58.33  cnf(c_0_23, plain, (k3_relat_1(X1)=k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 58.15/58.33  cnf(c_0_24, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 58.15/58.33  cnf(c_0_25, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 58.15/58.33  fof(c_0_26, negated_conjecture, (v1_relat_1(esk2_0)&k3_relat_1(esk2_0)!=k3_relat_1(k4_relat_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 58.15/58.33  cnf(c_0_27, plain, (X3=k3_tarski(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_16]), c_0_17])).
% 58.15/58.33  cnf(c_0_28, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.15/58.33  cnf(c_0_29, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k2_enumset1(X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_16]), c_0_17])).
% 58.15/58.33  cnf(c_0_30, plain, (k3_tarski(k2_enumset1(k1_relat_1(k4_relat_1(X1)),k1_relat_1(k4_relat_1(X1)),k1_relat_1(k4_relat_1(X1)),k1_relat_1(X1)))=k3_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 58.15/58.33  cnf(c_0_31, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 58.15/58.33  cnf(c_0_32, negated_conjecture, (k3_relat_1(esk2_0)!=k3_relat_1(k4_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 58.15/58.33  cnf(c_0_33, plain, (X1=X2|r2_hidden(esk1_3(X3,X4,X2),X3)|r2_hidden(esk1_3(X3,X4,X2),X4)|r2_hidden(esk1_3(X3,X4,X2),X2)|r2_hidden(esk1_3(X3,X4,X1),X3)|r2_hidden(esk1_3(X3,X4,X1),X4)|r2_hidden(esk1_3(X3,X4,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 58.15/58.33  cnf(c_0_34, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.15/58.33  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_enumset1(X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_16]), c_0_17])).
% 58.15/58.33  cnf(c_0_36, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_29])).
% 58.15/58.33  cnf(c_0_37, plain, (k3_tarski(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k1_relat_1(X1)))=k3_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 58.15/58.33  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(k4_relat_1(esk2_0)))|r2_hidden(esk1_3(X1,X2,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X2,k3_relat_1(k4_relat_1(esk2_0))),X2)|r2_hidden(esk1_3(X1,X2,k3_relat_1(k4_relat_1(esk2_0))),X1)|r2_hidden(esk1_3(X1,X2,k3_relat_1(esk2_0)),X2)|r2_hidden(esk1_3(X1,X2,k3_relat_1(esk2_0)),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])])).
% 58.15/58.33  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_enumset1(X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_16]), c_0_17])).
% 58.15/58.33  cnf(c_0_40, plain, (r2_hidden(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_35])).
% 58.15/58.33  cnf(c_0_41, plain, (r2_hidden(X1,k1_relat_1(X2))|r2_hidden(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k3_relat_1(k4_relat_1(X2)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 58.15/58.33  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(k4_relat_1(esk2_0)))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),X1)|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1)), inference(ef,[status(thm)],[c_0_38])).
% 58.15/58.33  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 58.15/58.33  cnf(c_0_44, plain, (X1=k3_tarski(k2_enumset1(X2,X2,X2,X2))|r2_hidden(esk1_3(X2,X2,X1),X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(ef,[status(thm)],[c_0_27])).
% 58.15/58.33  cnf(c_0_45, plain, (r2_hidden(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_39])).
% 58.15/58.33  cnf(c_0_46, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_40, c_0_23])).
% 58.15/58.33  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k2_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),X1)|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 58.15/58.33  cnf(c_0_48, plain, (r2_hidden(esk1_3(X1,X1,X2),X2)|r2_hidden(esk1_3(X1,X1,X2),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_40, c_0_44])).
% 58.15/58.33  cnf(c_0_49, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.15/58.33  cnf(c_0_50, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_45, c_0_23])).
% 58.15/58.33  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_43])]), c_0_48])).
% 58.15/58.33  cnf(c_0_52, plain, (X3=k3_tarski(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_16]), c_0_17])).
% 58.15/58.33  cnf(c_0_53, plain, (r2_hidden(X1,k3_relat_1(k4_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_25])).
% 58.15/58.33  cnf(c_0_54, plain, (r2_hidden(X1,k2_relat_1(X2))|r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k3_relat_1(X2))), inference(spm,[status(thm)],[c_0_36, c_0_23])).
% 58.15/58.33  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_43])])).
% 58.15/58.33  cnf(c_0_56, plain, (k3_relat_1(k4_relat_1(X1))=k3_tarski(k2_enumset1(X2,X2,X2,X3))|~v1_relat_1(X1)|~r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),k2_relat_1(X1))|~r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 58.15/58.33  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k2_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_43])])).
% 58.15/58.33  cnf(c_0_58, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_27])).
% 58.15/58.33  cnf(c_0_59, negated_conjecture, (k3_tarski(k2_enumset1(X1,X1,X1,X1))=k3_relat_1(k4_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,X1,k3_relat_1(esk2_0)),X1)|~r2_hidden(esk1_3(X1,X1,k3_relat_1(k4_relat_1(esk2_0))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_43])])).
% 58.15/58.33  cnf(c_0_60, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_58]), c_0_58])).
% 58.15/58.33  cnf(c_0_61, negated_conjecture, (k3_tarski(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)))=k3_relat_1(k4_relat_1(esk2_0))|r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))|r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_55])).
% 58.15/58.33  cnf(c_0_62, plain, (r2_hidden(X1,k3_relat_1(k4_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_24]), c_0_25])).
% 58.15/58.33  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(k4_relat_1(esk2_0))),k1_relat_1(esk2_0))|r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_32])).
% 58.15/58.33  cnf(c_0_64, plain, (k3_relat_1(k4_relat_1(X1))=k3_tarski(k2_enumset1(X2,X2,X2,X3))|~v1_relat_1(X1)|~r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),k1_relat_1(X1))|~r2_hidden(esk1_3(X2,X3,k3_relat_1(k4_relat_1(X1))),X3)), inference(spm,[status(thm)],[c_0_52, c_0_62])).
% 58.15/58.33  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(k4_relat_1(esk2_0))),k3_relat_1(esk2_0))|r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_63]), c_0_43])])).
% 58.15/58.33  cnf(c_0_66, negated_conjecture, (k3_tarski(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)))=k3_relat_1(k4_relat_1(esk2_0))|r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_63]), c_0_43])]), c_0_65])).
% 58.15/58.33  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_3(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_66]), c_0_32])).
% 58.15/58.33  cnf(c_0_68, plain, (X1=k3_tarski(k2_enumset1(X2,X2,X2,k1_relat_1(X3)))|r2_hidden(esk1_3(X2,k1_relat_1(X3),X1),k3_relat_1(X3))|r2_hidden(esk1_3(X2,k1_relat_1(X3),X1),X2)|r2_hidden(esk1_3(X2,k1_relat_1(X3),X1),X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_50, c_0_27])).
% 58.15/58.33  cnf(c_0_69, negated_conjecture, (k3_tarski(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0)))=k3_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_67]), c_0_67])])).
% 58.15/58.33  cnf(c_0_70, negated_conjecture, (X1=k3_tarski(k2_enumset1(X2,X2,X2,k1_relat_1(esk2_0)))|r2_hidden(esk1_3(X2,k1_relat_1(esk2_0),X1),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X2,k1_relat_1(esk2_0),X1),X1)|r2_hidden(esk1_3(X2,k1_relat_1(esk2_0),X1),X2)), inference(spm,[status(thm)],[c_0_68, c_0_43])).
% 58.15/58.33  cnf(c_0_71, negated_conjecture, (k3_tarski(k2_enumset1(X1,X1,X1,k1_relat_1(esk2_0)))=k3_relat_1(esk2_0)|r2_hidden(esk1_3(X1,k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|r2_hidden(esk1_3(X1,k1_relat_1(esk2_0),k3_relat_1(esk2_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_69]), c_0_69]), c_0_69]), c_0_69])])).
% 58.15/58.33  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k2_relat_1(esk2_0))|r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_71]), c_0_43])]), c_0_32])).
% 58.15/58.33  cnf(c_0_73, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.15/58.33  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_72]), c_0_43])])).
% 58.15/58.33  cnf(c_0_75, plain, (X3=k3_tarski(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_16]), c_0_17])).
% 58.15/58.33  cnf(c_0_76, negated_conjecture, (k3_tarski(k2_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k1_relat_1(esk2_0)))=k3_relat_1(esk2_0)|~r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_52, c_0_74])).
% 58.15/58.33  cnf(c_0_77, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k3_tarski(k2_enumset1(X3,X3,X3,X4))|~r2_hidden(esk1_3(X3,X4,k3_tarski(k2_enumset1(X1,X1,X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k3_tarski(k2_enumset1(X1,X1,X1,X2))),X2)), inference(spm,[status(thm)],[c_0_75, c_0_40])).
% 58.15/58.33  cnf(c_0_78, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k1_relat_1(esk2_0))|r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_74]), c_0_43])])).
% 58.15/58.33  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k1_relat_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_76]), c_0_43])]), c_0_32])).
% 58.15/58.33  cnf(c_0_80, plain, (k3_relat_1(X1)=k3_tarski(k2_enumset1(X2,X2,X2,X3))|~v1_relat_1(X1)|~r2_hidden(esk1_3(X2,X3,k3_relat_1(X1)),k2_relat_1(X1))|~r2_hidden(esk1_3(X2,X3,k3_relat_1(X1)),X2)), inference(spm,[status(thm)],[c_0_77, c_0_23])).
% 58.15/58.33  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_3(k2_relat_1(esk2_0),k1_relat_1(esk2_0),k3_relat_1(esk2_0)),k2_relat_1(esk2_0))), inference(sr,[status(thm)],[c_0_78, c_0_79])).
% 58.15/58.33  cnf(c_0_82, negated_conjecture, (k3_tarski(k2_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k1_relat_1(esk2_0)))=k3_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_43]), c_0_81])])).
% 58.15/58.33  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_82]), c_0_43])]), c_0_32]), ['proof']).
% 58.15/58.33  # SZS output end CNFRefutation
% 58.15/58.33  # Proof object total steps             : 84
% 58.15/58.33  # Proof object clause steps            : 67
% 58.15/58.33  # Proof object formula steps           : 17
% 58.15/58.33  # Proof object conjectures             : 28
% 58.15/58.33  # Proof object clause conjectures      : 25
% 58.15/58.33  # Proof object formula conjectures     : 3
% 58.15/58.33  # Proof object initial clauses used    : 15
% 58.15/58.33  # Proof object initial formulas used   : 8
% 58.15/58.33  # Proof object generating inferences   : 40
% 58.15/58.33  # Proof object simplifying inferences  : 65
% 58.15/58.33  # Training examples: 0 positive, 0 negative
% 58.15/58.33  # Parsed axioms                        : 8
% 58.15/58.33  # Removed by relevancy pruning/SinE    : 0
% 58.15/58.33  # Initial clauses                      : 15
% 58.15/58.33  # Removed in clause preprocessing      : 3
% 58.15/58.33  # Initial clauses in saturation        : 12
% 58.15/58.33  # Processed clauses                    : 18685
% 58.15/58.33  # ...of these trivial                  : 9
% 58.15/58.33  # ...subsumed                          : 11154
% 58.15/58.33  # ...remaining for further processing  : 7522
% 58.15/58.33  # Other redundant clauses eliminated   : 7
% 58.15/58.33  # Clauses deleted for lack of memory   : 71857
% 58.15/58.33  # Backward-subsumed                    : 1572
% 58.15/58.33  # Backward-rewritten                   : 6
% 58.15/58.33  # Generated clauses                    : 2020768
% 58.15/58.33  # ...of the previous two non-trivial   : 1996610
% 58.15/58.33  # Contextual simplify-reflections      : 629
% 58.15/58.33  # Paramodulations                      : 2019736
% 58.15/58.33  # Factorizations                       : 1024
% 58.15/58.33  # Equation resolutions                 : 7
% 58.15/58.33  # Propositional unsat checks           : 1
% 58.15/58.33  #    Propositional check models        : 0
% 58.15/58.33  #    Propositional check unsatisfiable : 0
% 58.15/58.33  #    Propositional clauses             : 0
% 58.15/58.33  #    Propositional clauses after purity: 0
% 58.15/58.33  #    Propositional unsat core size     : 0
% 58.15/58.33  #    Propositional preprocessing time  : 0.000
% 58.15/58.33  #    Propositional encoding time       : 1.353
% 58.15/58.33  #    Propositional solver time         : 0.054
% 58.15/58.33  #    Success case prop preproc time    : 0.000
% 58.15/58.33  #    Success case prop encoding time   : 0.000
% 58.15/58.33  #    Success case prop solver time     : 0.000
% 58.15/58.33  # Current number of processed clauses  : 5928
% 58.15/58.33  #    Positive orientable unit clauses  : 12
% 58.15/58.33  #    Positive unorientable unit clauses: 0
% 58.15/58.33  #    Negative unit clauses             : 2
% 58.15/58.33  #    Non-unit-clauses                  : 5914
% 58.15/58.33  # Current number of unprocessed clauses: 1127608
% 58.15/58.33  # ...number of literals in the above   : 9889180
% 58.15/58.33  # Current number of archived formulas  : 0
% 58.15/58.33  # Current number of archived clauses   : 1594
% 58.15/58.33  # Clause-clause subsumption calls (NU) : 4953697
% 58.15/58.33  # Rec. Clause-clause subsumption calls : 864573
% 58.15/58.33  # Non-unit clause-clause subsumptions  : 13344
% 58.15/58.33  # Unit Clause-clause subsumption calls : 7408
% 58.15/58.33  # Rewrite failures with RHS unbound    : 0
% 58.15/58.33  # BW rewrite match attempts            : 259
% 58.15/58.33  # BW rewrite match successes           : 5
% 58.15/58.33  # Condensation attempts                : 0
% 58.15/58.33  # Condensation successes               : 0
% 58.15/58.33  # Termbank termtop insertions          : 150573369
% 58.24/58.43  
% 58.24/58.43  # -------------------------------------------------
% 58.24/58.43  # User time                : 57.016 s
% 58.24/58.43  # System time              : 1.065 s
% 58.24/58.43  # Total time               : 58.081 s
% 58.24/58.43  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
