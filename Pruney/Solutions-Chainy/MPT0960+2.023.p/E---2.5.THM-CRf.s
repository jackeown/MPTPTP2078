%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of clauses        :   26 (  42 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 161 expanded)
%              Number of equality atoms :   58 (  95 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   33 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t30_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,k3_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(c_0_12,plain,(
    ! [X17,X18] : k1_setfam_1(k2_tarski(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | k2_wellord1(X19,X20) = k3_xboole_0(X19,k2_zfmisc_1(X20,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

fof(c_0_23,plain,(
    ! [X22,X23,X24,X25] :
      ( ( k3_relat_1(X23) = X22
        | X23 != k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X23)
        | r1_tarski(X24,X25)
        | ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X25,X22)
        | X23 != k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_tarski(X24,X25)
        | r2_hidden(k4_tarski(X24,X25),X23)
        | ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X25,X22)
        | X23 != k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk1_2(X22,X23),X22)
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk2_2(X22,X23),X22)
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)
        | ~ r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)
        | r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_24,plain,(
    ! [X28] : v1_relat_1(k1_wellord2(X28)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_25,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_27,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k2_wellord1(X21,k3_relat_1(X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_wellord1])])).

cnf(c_0_33,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_40,plain,
    ( k2_wellord1(X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_20]),c_0_30])).

cnf(c_0_41,plain,
    ( k2_wellord1(X1,k3_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_29]),c_0_30])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_20]),c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k1_wellord2(esk3_0),k1_setfam_1(k2_enumset1(k1_wellord2(esk3_0),k1_wellord2(esk3_0),k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0)))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k2_enumset1(k1_wellord2(X1),k1_wellord2(X1),k1_wellord2(X1),k2_zfmisc_1(X2,X2))) = k2_wellord1(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_48,plain,
    ( k2_wellord1(k1_wellord2(X1),X1) = k1_wellord2(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_34]),c_0_42])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.042 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(t33_wellord2, conjecture, ![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 0.13/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 0.13/0.39  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.13/0.39  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.39  fof(t30_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>k2_wellord1(X1,k3_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 0.13/0.39  fof(c_0_12, plain, ![X17, X18]:k1_setfam_1(k2_tarski(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.39  fof(c_0_13, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_14, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(assume_negation,[status(cth)],[t33_wellord2])).
% 0.13/0.39  fof(c_0_18, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.39  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_20, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  fof(c_0_21, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X19, X20]:(~v1_relat_1(X19)|k2_wellord1(X19,X20)=k3_xboole_0(X19,k2_zfmisc_1(X20,X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.13/0.39  fof(c_0_23, plain, ![X22, X23, X24, X25]:(((k3_relat_1(X23)=X22|X23!=k1_wellord2(X22)|~v1_relat_1(X23))&((~r2_hidden(k4_tarski(X24,X25),X23)|r1_tarski(X24,X25)|(~r2_hidden(X24,X22)|~r2_hidden(X25,X22))|X23!=k1_wellord2(X22)|~v1_relat_1(X23))&(~r1_tarski(X24,X25)|r2_hidden(k4_tarski(X24,X25),X23)|(~r2_hidden(X24,X22)|~r2_hidden(X25,X22))|X23!=k1_wellord2(X22)|~v1_relat_1(X23))))&(((r2_hidden(esk1_2(X22,X23),X22)|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))&(r2_hidden(esk2_2(X22,X23),X22)|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23)))&((~r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)|~r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)|r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.13/0.39  fof(c_0_24, plain, ![X28]:v1_relat_1(k1_wellord2(X28)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.13/0.39  fof(c_0_25, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  fof(c_0_26, plain, ![X5]:k3_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.39  fof(c_0_27, negated_conjecture, ~r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.39  cnf(c_0_28, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_31, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_32, plain, ![X21]:(~v1_relat_1(X21)|k2_wellord1(X21,k3_relat_1(X21))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_wellord1])])).
% 0.13/0.39  cnf(c_0_33, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_34, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_37, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (~r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_39, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.13/0.39  cnf(c_0_40, plain, (k2_wellord1(X1,X2)=k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(X2,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_20]), c_0_30])).
% 0.13/0.39  cnf(c_0_41, plain, (k2_wellord1(X1,k3_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_42, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])])).
% 0.13/0.39  cnf(c_0_43, plain, (k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_29]), c_0_30])).
% 0.13/0.39  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_45, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_20]), c_0_30])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k1_wellord2(esk3_0),k1_setfam_1(k2_enumset1(k1_wellord2(esk3_0),k1_wellord2(esk3_0),k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_47, plain, (k1_setfam_1(k2_enumset1(k1_wellord2(X1),k1_wellord2(X1),k1_wellord2(X1),k2_zfmisc_1(X2,X2)))=k2_wellord1(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.13/0.39  cnf(c_0_48, plain, (k2_wellord1(k1_wellord2(X1),X1)=k1_wellord2(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_34]), c_0_42])).
% 0.13/0.39  cnf(c_0_49, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 51
% 0.13/0.39  # Proof object clause steps            : 26
% 0.13/0.39  # Proof object formula steps           : 25
% 0.13/0.39  # Proof object conjectures             : 6
% 0.13/0.39  # Proof object clause conjectures      : 3
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 13
% 0.13/0.39  # Proof object initial formulas used   : 12
% 0.13/0.39  # Proof object generating inferences   : 4
% 0.13/0.39  # Proof object simplifying inferences  : 20
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 12
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 21
% 0.13/0.39  # Removed in clause preprocessing      : 4
% 0.13/0.39  # Initial clauses in saturation        : 17
% 0.13/0.39  # Processed clauses                    : 49
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 48
% 0.13/0.39  # Other redundant clauses eliminated   : 9
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 30
% 0.13/0.39  # ...of the previous two non-trivial   : 28
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 21
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 9
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 22
% 0.13/0.39  #    Positive orientable unit clauses  : 7
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 14
% 0.13/0.39  # Current number of unprocessed clauses: 12
% 0.13/0.39  # ...number of literals in the above   : 57
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 21
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 79
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 41
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 15
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 5
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1999
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.047 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
