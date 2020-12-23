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
% DateTime   : Thu Dec  3 10:41:30 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 297 expanded)
%              Number of clauses        :   39 ( 141 expanded)
%              Number of leaves         :   10 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  133 ( 518 expanded)
%              Number of equality atoms :   45 ( 286 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_17,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_18])).

cnf(c_0_22,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k3_tarski(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk5_0,esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( X3 = k3_tarski(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_18])).

fof(c_0_26,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r1_xboole_0(X16,X17)
        | r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X21,k3_xboole_0(X19,X20))
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_27,plain,(
    ! [X24] : r1_xboole_0(X24,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_28,plain,(
    ! [X22] : k2_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),X1),k1_enumset1(esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),X1),esk5_0)
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k1_enumset1(X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_36,plain,
    ( X3 = k3_tarski(k1_enumset1(X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),esk5_0) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24])]),c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,k3_xboole_0(X3,k1_xboole_0)),X1)
    | r2_hidden(esk1_3(X1,X2,k3_xboole_0(X3,k1_xboole_0)),X2)
    | ~ r2_hidden(X4,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_38])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k3_tarski(k1_enumset1(esk5_0,esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k1_enumset1(X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_3(k1_xboole_0,X1,k3_xboole_0(X2,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk1_3(k1_xboole_0,X1,k3_xboole_0(X2,k1_xboole_0)),X1)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_24])).

fof(c_0_49,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,X31)
        | ~ r1_tarski(k2_tarski(X29,X30),X31) )
      & ( r2_hidden(X30,X31)
        | ~ r1_tarski(k2_tarski(X29,X30),X31) )
      & ( ~ r2_hidden(X29,X31)
        | ~ r2_hidden(X30,X31)
        | r1_tarski(k2_tarski(X29,X30),X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_39])).

fof(c_0_54,plain,(
    ! [X23] : r1_tarski(k1_xboole_0,X23) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_38,c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n022.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 14:26:55 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.17/0.35  # and selection function SelectCQIArNpEqFirst.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.027 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.17/0.35  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.17/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.17/0.35  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.17/0.35  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.17/0.35  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.17/0.35  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.17/0.35  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.17/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.17/0.35  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.17/0.35  fof(c_0_11, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.17/0.35  fof(c_0_12, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.35  fof(c_0_13, negated_conjecture, k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.17/0.35  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.35  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.17/0.35  cnf(c_0_17, negated_conjecture, (k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.35  cnf(c_0_18, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.35  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.35  fof(c_0_20, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.17/0.35  cnf(c_0_21, negated_conjecture, (k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_18])).
% 0.17/0.35  cnf(c_0_22, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k3_tarski(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18]), c_0_18])).
% 0.17/0.35  cnf(c_0_23, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.35  cnf(c_0_24, negated_conjecture, (k3_tarski(k1_enumset1(esk5_0,esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.17/0.35  cnf(c_0_25, plain, (X3=k3_tarski(k1_enumset1(X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_23, c_0_18])).
% 0.17/0.35  fof(c_0_26, plain, ![X16, X17, X19, X20, X21]:((r1_xboole_0(X16,X17)|r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)))&(~r2_hidden(X21,k3_xboole_0(X19,X20))|~r1_xboole_0(X19,X20))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.17/0.35  fof(c_0_27, plain, ![X24]:r1_xboole_0(X24,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.17/0.35  fof(c_0_28, plain, ![X22]:k2_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.17/0.35  cnf(c_0_29, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.35  cnf(c_0_30, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.35  cnf(c_0_31, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),X1),k1_enumset1(esk3_0,esk3_0,esk4_0))|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),X1),esk5_0)|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),X1),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.17/0.35  cnf(c_0_32, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.35  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.35  cnf(c_0_34, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.35  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k1_enumset1(X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.17/0.35  cnf(c_0_36, plain, (X3=k3_tarski(k1_enumset1(X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_30, c_0_18])).
% 0.17/0.35  cnf(c_0_37, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),esk5_0)), inference(ef,[status(thm)],[c_0_31])).
% 0.17/0.35  cnf(c_0_38, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.17/0.35  cnf(c_0_39, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_34, c_0_18])).
% 0.17/0.35  cnf(c_0_40, plain, (r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_35])).
% 0.17/0.35  cnf(c_0_41, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_24])]), c_0_37])).
% 0.17/0.35  cnf(c_0_42, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.35  cnf(c_0_43, plain, (r2_hidden(esk1_3(X1,X2,k3_xboole_0(X3,k1_xboole_0)),X1)|r2_hidden(esk1_3(X1,X2,k3_xboole_0(X3,k1_xboole_0)),X2)|~r2_hidden(X4,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_25]), c_0_38])).
% 0.17/0.35  cnf(c_0_44, plain, (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_39, c_0_22])).
% 0.17/0.35  cnf(c_0_45, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k3_tarski(k1_enumset1(esk5_0,esk5_0,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.17/0.35  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k1_enumset1(X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_18])).
% 0.17/0.35  cnf(c_0_47, plain, (r2_hidden(esk1_3(k1_xboole_0,X1,k3_xboole_0(X2,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk1_3(k1_xboole_0,X1,k3_xboole_0(X2,k1_xboole_0)),X1)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.17/0.35  cnf(c_0_48, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk1_3(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_24])).
% 0.17/0.35  fof(c_0_49, plain, ![X29, X30, X31]:(((r2_hidden(X29,X31)|~r1_tarski(k2_tarski(X29,X30),X31))&(r2_hidden(X30,X31)|~r1_tarski(k2_tarski(X29,X30),X31)))&(~r2_hidden(X29,X31)|~r2_hidden(X30,X31)|r1_tarski(k2_tarski(X29,X30),X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.17/0.35  cnf(c_0_50, plain, (r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_46])).
% 0.17/0.35  cnf(c_0_51, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.17/0.35  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.35  cnf(c_0_53, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_39])).
% 0.17/0.35  fof(c_0_54, plain, ![X23]:r1_tarski(k1_xboole_0,X23), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.17/0.35  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X3,X3,X1),X2)), inference(rw,[status(thm)],[c_0_52, c_0_15])).
% 0.17/0.35  cnf(c_0_56, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_53])).
% 0.17/0.35  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.17/0.35  cnf(c_0_58, negated_conjecture, (r2_hidden(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.17/0.35  cnf(c_0_59, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_38, c_0_58]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 60
% 0.17/0.35  # Proof object clause steps            : 39
% 0.17/0.35  # Proof object formula steps           : 21
% 0.17/0.35  # Proof object conjectures             : 16
% 0.17/0.35  # Proof object clause conjectures      : 13
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 13
% 0.17/0.35  # Proof object initial formulas used   : 10
% 0.17/0.35  # Proof object generating inferences   : 14
% 0.17/0.35  # Proof object simplifying inferences  : 21
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 10
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 18
% 0.17/0.35  # Removed in clause preprocessing      : 2
% 0.17/0.35  # Initial clauses in saturation        : 16
% 0.17/0.35  # Processed clauses                    : 77
% 0.17/0.35  # ...of these trivial                  : 1
% 0.17/0.35  # ...subsumed                          : 15
% 0.17/0.35  # ...remaining for further processing  : 61
% 0.17/0.35  # Other redundant clauses eliminated   : 3
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 2
% 0.17/0.35  # Backward-rewritten                   : 10
% 0.17/0.35  # Generated clauses                    : 261
% 0.17/0.35  # ...of the previous two non-trivial   : 248
% 0.17/0.35  # Contextual simplify-reflections      : 2
% 0.17/0.35  # Paramodulations                      : 250
% 0.17/0.35  # Factorizations                       : 8
% 0.17/0.35  # Equation resolutions                 : 3
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 30
% 0.17/0.35  #    Positive orientable unit clauses  : 7
% 0.17/0.35  #    Positive unorientable unit clauses: 1
% 0.17/0.35  #    Negative unit clauses             : 1
% 0.17/0.35  #    Non-unit-clauses                  : 21
% 0.17/0.35  # Current number of unprocessed clauses: 200
% 0.17/0.35  # ...number of literals in the above   : 760
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 30
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 151
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 117
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 19
% 0.17/0.35  # Unit Clause-clause subsumption calls : 5
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 10
% 0.17/0.35  # BW rewrite match successes           : 9
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 6152
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.035 s
% 0.17/0.35  # System time              : 0.004 s
% 0.17/0.35  # Total time               : 0.039 s
% 0.17/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
