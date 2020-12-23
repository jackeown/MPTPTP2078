%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:32 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 386 expanded)
%              Number of clauses        :   38 ( 185 expanded)
%              Number of leaves         :    6 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 (1272 expanded)
%              Number of equality atoms :   32 ( 421 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t91_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_6,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_7,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t91_relat_1])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,k1_relat_1(esk4_0))
    & k1_relat_1(k7_relat_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_15,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k1_relat_1(X27))
        | r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( X1 = X2
    | r2_hidden(esk2_3(X3,X4,X2),X4)
    | r2_hidden(esk2_3(X3,X4,X2),X2)
    | r2_hidden(esk2_3(X3,X4,X1),X4)
    | r2_hidden(esk2_3(X3,X4,X1),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_15])).

cnf(c_0_20,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0)))
    | r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X2)
    | r2_hidden(esk2_3(X1,X2,esk3_0),esk3_0)
    | r2_hidden(esk2_3(X1,X2,esk3_0),X2) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)
    | r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X2)
    | r2_hidden(esk2_3(X1,X2,esk3_0),esk3_0)
    | r2_hidden(esk2_3(X1,X2,esk3_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_3(X1,esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)
    | r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk3_0) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0)) = k1_relat_1(k7_relat_1(esk4_0,esk3_0))
    | r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(esk4_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1)))
    | ~ r2_hidden(esk1_2(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24])])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_37]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,esk3_0),X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_46,plain,
    ( X1 = X2
    | r2_hidden(esk2_3(X1,X2,X1),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_45])]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_47]),c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_48]),c_0_24])]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:39:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.17/0.45  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.17/0.45  #
% 0.17/0.45  # Preprocessing time       : 0.027 s
% 0.17/0.45  # Presaturation interreduction done
% 0.17/0.45  
% 0.17/0.45  # Proof found!
% 0.17/0.45  # SZS status Theorem
% 0.17/0.45  # SZS output start CNFRefutation
% 0.17/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.17/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.45  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.17/0.45  fof(t91_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.17/0.45  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.17/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.17/0.45  fof(c_0_6, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.17/0.45  fof(c_0_7, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.45  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.17/0.45  cnf(c_0_9, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.45  cnf(c_0_10, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.45  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t91_relat_1])).
% 0.17/0.45  cnf(c_0_12, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.45  cnf(c_0_13, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.17/0.45  fof(c_0_14, negated_conjecture, (v1_relat_1(esk4_0)&(r1_tarski(esk3_0,k1_relat_1(esk4_0))&k1_relat_1(k7_relat_1(esk4_0,esk3_0))!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.17/0.45  cnf(c_0_15, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.17/0.45  cnf(c_0_16, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.45  fof(c_0_17, plain, ![X25, X26, X27]:(((r2_hidden(X25,X26)|~r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))|~v1_relat_1(X27))&(r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))|~v1_relat_1(X27)))&(~r2_hidden(X25,X26)|~r2_hidden(X25,k1_relat_1(X27))|r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.17/0.45  cnf(c_0_18, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.45  cnf(c_0_19, plain, (X1=X2|r2_hidden(esk2_3(X3,X4,X2),X4)|r2_hidden(esk2_3(X3,X4,X2),X2)|r2_hidden(esk2_3(X3,X4,X1),X4)|r2_hidden(esk2_3(X3,X4,X1),X1)), inference(spm,[status(thm)],[c_0_15, c_0_15])).
% 0.17/0.45  cnf(c_0_20, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.45  cnf(c_0_21, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_16, c_0_13])).
% 0.17/0.45  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.45  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0)))|r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X2)|r2_hidden(esk2_3(X1,X2,esk3_0),esk3_0)|r2_hidden(esk2_3(X1,X2,esk3_0),X2)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19])])).
% 0.17/0.45  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.45  fof(c_0_25, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.17/0.45  cnf(c_0_26, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_20, c_0_13])).
% 0.17/0.45  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_21])).
% 0.17/0.45  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)|r2_hidden(esk2_3(X1,X2,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X2)|r2_hidden(esk2_3(X1,X2,esk3_0),esk3_0)|r2_hidden(esk2_3(X1,X2,esk3_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.17/0.45  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.45  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.45  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_27])).
% 0.17/0.45  cnf(c_0_32, negated_conjecture, (r2_hidden(esk2_3(X1,esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)|r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk3_0)), inference(ef,[status(thm)],[c_0_28])).
% 0.17/0.45  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.45  cnf(c_0_34, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.45  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.17/0.45  cnf(c_0_36, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.45  cnf(c_0_37, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_15])).
% 0.17/0.45  cnf(c_0_38, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0))=k1_relat_1(k7_relat_1(esk4_0,esk3_0))|r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.17/0.45  cnf(c_0_39, plain, (r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)|~r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))|~r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.17/0.45  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(esk4_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.17/0.45  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_18])).
% 0.17/0.45  cnf(c_0_42, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1)))|~r2_hidden(esk1_2(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_24])])).
% 0.17/0.45  cnf(c_0_43, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_37]), c_0_37])).
% 0.17/0.45  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,esk3_0),X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_41])).
% 0.17/0.45  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_42, c_0_30])).
% 0.17/0.45  cnf(c_0_46, plain, (X1=X2|r2_hidden(esk2_3(X1,X2,X1),X1)|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(spm,[status(thm)],[c_0_43, c_0_27])).
% 0.17/0.45  cnf(c_0_47, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.17/0.45  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_44]), c_0_45])]), c_0_18])).
% 0.17/0.45  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk2_3(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_47]), c_0_18])).
% 0.17/0.45  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_48]), c_0_24])]), c_0_49]), ['proof']).
% 0.17/0.45  # SZS output end CNFRefutation
% 0.17/0.45  # Proof object total steps             : 51
% 0.17/0.45  # Proof object clause steps            : 38
% 0.17/0.45  # Proof object formula steps           : 13
% 0.17/0.45  # Proof object conjectures             : 19
% 0.17/0.45  # Proof object clause conjectures      : 16
% 0.17/0.45  # Proof object formula conjectures     : 3
% 0.17/0.45  # Proof object initial clauses used    : 13
% 0.17/0.45  # Proof object initial formulas used   : 6
% 0.17/0.45  # Proof object generating inferences   : 21
% 0.17/0.45  # Proof object simplifying inferences  : 21
% 0.17/0.45  # Training examples: 0 positive, 0 negative
% 0.17/0.45  # Parsed axioms                        : 7
% 0.17/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.45  # Initial clauses                      : 18
% 0.17/0.45  # Removed in clause preprocessing      : 2
% 0.17/0.45  # Initial clauses in saturation        : 16
% 0.17/0.45  # Processed clauses                    : 302
% 0.17/0.45  # ...of these trivial                  : 6
% 0.17/0.45  # ...subsumed                          : 106
% 0.17/0.45  # ...remaining for further processing  : 190
% 0.17/0.45  # Other redundant clauses eliminated   : 5
% 0.17/0.45  # Clauses deleted for lack of memory   : 0
% 0.17/0.45  # Backward-subsumed                    : 0
% 0.17/0.45  # Backward-rewritten                   : 2
% 0.17/0.45  # Generated clauses                    : 3733
% 0.17/0.45  # ...of the previous two non-trivial   : 3559
% 0.17/0.45  # Contextual simplify-reflections      : 2
% 0.17/0.45  # Paramodulations                      : 3656
% 0.17/0.45  # Factorizations                       : 72
% 0.17/0.45  # Equation resolutions                 : 5
% 0.17/0.45  # Propositional unsat checks           : 0
% 0.17/0.45  #    Propositional check models        : 0
% 0.17/0.45  #    Propositional check unsatisfiable : 0
% 0.17/0.45  #    Propositional clauses             : 0
% 0.17/0.45  #    Propositional clauses after purity: 0
% 0.17/0.45  #    Propositional unsat core size     : 0
% 0.17/0.45  #    Propositional preprocessing time  : 0.000
% 0.17/0.45  #    Propositional encoding time       : 0.000
% 0.17/0.45  #    Propositional solver time         : 0.000
% 0.17/0.45  #    Success case prop preproc time    : 0.000
% 0.17/0.45  #    Success case prop encoding time   : 0.000
% 0.17/0.45  #    Success case prop solver time     : 0.000
% 0.17/0.45  # Current number of processed clauses  : 169
% 0.17/0.45  #    Positive orientable unit clauses  : 30
% 0.17/0.45  #    Positive unorientable unit clauses: 0
% 0.17/0.45  #    Negative unit clauses             : 2
% 0.17/0.45  #    Non-unit-clauses                  : 137
% 0.17/0.45  # Current number of unprocessed clauses: 3282
% 0.17/0.45  # ...number of literals in the above   : 16234
% 0.17/0.45  # Current number of archived formulas  : 0
% 0.17/0.45  # Current number of archived clauses   : 20
% 0.17/0.45  # Clause-clause subsumption calls (NU) : 2875
% 0.17/0.45  # Rec. Clause-clause subsumption calls : 2071
% 0.17/0.45  # Non-unit clause-clause subsumptions  : 108
% 0.17/0.45  # Unit Clause-clause subsumption calls : 140
% 0.17/0.45  # Rewrite failures with RHS unbound    : 0
% 0.17/0.45  # BW rewrite match attempts            : 85
% 0.17/0.45  # BW rewrite match successes           : 2
% 0.17/0.45  # Condensation attempts                : 0
% 0.17/0.45  # Condensation successes               : 0
% 0.17/0.45  # Termbank termtop insertions          : 76694
% 0.17/0.45  
% 0.17/0.45  # -------------------------------------------------
% 0.17/0.45  # User time                : 0.117 s
% 0.17/0.45  # System time              : 0.010 s
% 0.17/0.45  # Total time               : 0.127 s
% 0.17/0.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
