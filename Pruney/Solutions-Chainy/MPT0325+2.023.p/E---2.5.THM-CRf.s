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
% DateTime   : Thu Dec  3 10:44:08 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 405 expanded)
%              Number of clauses        :   44 ( 176 expanded)
%              Number of leaves         :    7 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  108 ( 775 expanded)
%              Number of equality atoms :   81 ( 480 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_9,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X16] : k2_zfmisc_1(k3_xboole_0(X13,X14),k3_xboole_0(X15,X16)) = k3_xboole_0(k2_zfmisc_1(X13,X15),k2_zfmisc_1(X14,X16)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_16])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk4_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_19]),c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X17 = X19
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | k2_zfmisc_1(X17,X18) != k2_zfmisc_1(X19,X20) )
      & ( X18 = X20
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | k2_zfmisc_1(X17,X18) != k2_zfmisc_1(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1),k3_xboole_0(k3_xboole_0(esk4_0,esk2_0),X2)) = k2_zfmisc_1(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk2_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_23]),c_0_19])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),k3_xboole_0(esk2_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1),k3_xboole_0(esk4_0,esk2_0)) = k2_zfmisc_1(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk4_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),k3_xboole_0(esk4_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_32]),c_0_19]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk1_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X2)
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(k3_xboole_0(esk1_0,X2),k3_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1) = k3_xboole_0(esk1_0,X1)
    | k3_xboole_0(esk1_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = esk2_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk1_0,esk3_0)) = k3_xboole_0(esk1_0,X1)
    | k3_xboole_0(esk1_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k3_xboole_0(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_47]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k3_xboole_0(esk1_0,esk1_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk1_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.18/4.40  # AutoSched0-Mode selected heuristic G_____X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN
% 4.18/4.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 4.18/4.40  #
% 4.18/4.40  # Preprocessing time       : 0.027 s
% 4.18/4.40  # Presaturation interreduction done
% 4.18/4.40  
% 4.18/4.40  # Proof found!
% 4.18/4.40  # SZS status Theorem
% 4.18/4.40  # SZS output start CNFRefutation
% 4.18/4.40  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 4.18/4.40  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.18/4.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.18/4.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.18/4.40  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 4.18/4.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.18/4.40  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 4.18/4.40  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 4.18/4.40  fof(c_0_8, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k3_xboole_0(X9,X10)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 4.18/4.40  fof(c_0_9, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 4.18/4.40  fof(c_0_10, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 4.18/4.40  fof(c_0_11, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 4.18/4.40  cnf(c_0_12, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.18/4.40  cnf(c_0_13, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.18/4.40  cnf(c_0_14, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.18/4.40  fof(c_0_15, plain, ![X13, X14, X15, X16]:k2_zfmisc_1(k3_xboole_0(X13,X14),k3_xboole_0(X15,X16))=k3_xboole_0(k2_zfmisc_1(X13,X15),k2_zfmisc_1(X14,X16)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 4.18/4.40  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.18/4.40  cnf(c_0_17, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 4.18/4.40  cnf(c_0_18, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 4.18/4.40  cnf(c_0_19, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.18/4.40  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_13, c_0_16])).
% 4.18/4.40  cnf(c_0_21, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 4.18/4.40  cnf(c_0_22, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 4.18/4.40  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk4_0,esk2_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16]), c_0_19]), c_0_16])).
% 4.18/4.40  cnf(c_0_24, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 4.18/4.40  cnf(c_0_25, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 4.18/4.40  cnf(c_0_26, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_22])).
% 4.18/4.40  fof(c_0_27, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 4.18/4.40  fof(c_0_28, plain, ![X17, X18, X19, X20]:((X17=X19|(X17=k1_xboole_0|X18=k1_xboole_0)|k2_zfmisc_1(X17,X18)!=k2_zfmisc_1(X19,X20))&(X18=X20|(X17=k1_xboole_0|X18=k1_xboole_0)|k2_zfmisc_1(X17,X18)!=k2_zfmisc_1(X19,X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 4.18/4.40  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1),k3_xboole_0(k3_xboole_0(esk4_0,esk2_0),X2))=k2_zfmisc_1(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk2_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_23]), c_0_19])).
% 4.18/4.40  cnf(c_0_30, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_24])).
% 4.18/4.40  cnf(c_0_31, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 4.18/4.40  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 4.18/4.40  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),k3_xboole_0(esk2_0,esk2_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 4.18/4.40  cnf(c_0_34, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.18/4.40  cnf(c_0_35, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.18/4.40  cnf(c_0_36, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.18/4.40  cnf(c_0_37, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.18/4.40  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1),k3_xboole_0(esk4_0,esk2_0))=k2_zfmisc_1(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk4_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 4.18/4.40  cnf(c_0_39, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.18/4.40  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),k3_xboole_0(esk4_0,esk2_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_32]), c_0_19]), c_0_16])).
% 4.18/4.40  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk1_0,esk1_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 4.18/4.40  cnf(c_0_42, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_36]), c_0_35])).
% 4.18/4.40  cnf(c_0_43, negated_conjecture, (X1=k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X2)|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(k3_xboole_0(esk1_0,X2),k3_xboole_0(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 4.18/4.40  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=X1|k2_zfmisc_1(esk1_0,esk2_0)!=k2_zfmisc_1(X2,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])).
% 4.18/4.40  cnf(c_0_45, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1)=k3_xboole_0(esk1_0,X1)|k3_xboole_0(esk1_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_42])).
% 4.18/4.40  cnf(c_0_46, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=esk2_0), inference(er,[status(thm)],[c_0_44])).
% 4.18/4.40  cnf(c_0_47, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk1_0,esk3_0))=k3_xboole_0(esk1_0,X1)|k3_xboole_0(esk1_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_45])).
% 4.18/4.40  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_40, c_0_46])).
% 4.18/4.40  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=k3_xboole_0(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_47]), c_0_41])).
% 4.18/4.40  cnf(c_0_50, negated_conjecture, (X1=k3_xboole_0(esk1_0,esk1_0)|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_48])).
% 4.18/4.40  cnf(c_0_51, negated_conjecture, (esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 4.18/4.40  cnf(c_0_52, negated_conjecture, (esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 4.18/4.40  cnf(c_0_53, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.18/4.40  cnf(c_0_54, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_46])).
% 4.18/4.40  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_49])).
% 4.18/4.40  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk1_0,esk1_0)=esk1_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_50]), c_0_51]), c_0_52])).
% 4.18/4.40  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 4.18/4.40  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_57]), ['proof']).
% 4.18/4.40  # SZS output end CNFRefutation
% 4.18/4.40  # Proof object total steps             : 59
% 4.18/4.40  # Proof object clause steps            : 44
% 4.18/4.40  # Proof object formula steps           : 15
% 4.18/4.40  # Proof object conjectures             : 32
% 4.18/4.40  # Proof object clause conjectures      : 29
% 4.18/4.40  # Proof object formula conjectures     : 3
% 4.18/4.40  # Proof object initial clauses used    : 11
% 4.18/4.40  # Proof object initial formulas used   : 7
% 4.18/4.40  # Proof object generating inferences   : 27
% 4.18/4.40  # Proof object simplifying inferences  : 22
% 4.18/4.40  # Training examples: 0 positive, 0 negative
% 4.18/4.40  # Parsed axioms                        : 7
% 4.18/4.40  # Removed by relevancy pruning/SinE    : 0
% 4.18/4.40  # Initial clauses                      : 12
% 4.18/4.40  # Removed in clause preprocessing      : 0
% 4.18/4.40  # Initial clauses in saturation        : 12
% 4.18/4.40  # Processed clauses                    : 40309
% 4.18/4.40  # ...of these trivial                  : 467
% 4.18/4.40  # ...subsumed                          : 36940
% 4.18/4.40  # ...remaining for further processing  : 2902
% 4.18/4.40  # Other redundant clauses eliminated   : 0
% 4.18/4.40  # Clauses deleted for lack of memory   : 0
% 4.18/4.40  # Backward-subsumed                    : 646
% 4.18/4.40  # Backward-rewritten                   : 1221
% 4.18/4.40  # Generated clauses                    : 669076
% 4.18/4.40  # ...of the previous two non-trivial   : 637897
% 4.18/4.40  # Contextual simplify-reflections      : 14
% 4.18/4.40  # Paramodulations                      : 669036
% 4.18/4.40  # Factorizations                       : 2
% 4.18/4.40  # Equation resolutions                 : 38
% 4.18/4.40  # Propositional unsat checks           : 0
% 4.18/4.40  #    Propositional check models        : 0
% 4.18/4.40  #    Propositional check unsatisfiable : 0
% 4.18/4.40  #    Propositional clauses             : 0
% 4.18/4.40  #    Propositional clauses after purity: 0
% 4.18/4.40  #    Propositional unsat core size     : 0
% 4.18/4.40  #    Propositional preprocessing time  : 0.000
% 4.18/4.40  #    Propositional encoding time       : 0.000
% 4.18/4.40  #    Propositional solver time         : 0.000
% 4.18/4.40  #    Success case prop preproc time    : 0.000
% 4.18/4.40  #    Success case prop encoding time   : 0.000
% 4.18/4.40  #    Success case prop solver time     : 0.000
% 4.18/4.40  # Current number of processed clauses  : 1023
% 4.18/4.40  #    Positive orientable unit clauses  : 92
% 4.18/4.40  #    Positive unorientable unit clauses: 1
% 4.18/4.40  #    Negative unit clauses             : 4
% 4.18/4.40  #    Non-unit-clauses                  : 926
% 4.18/4.40  # Current number of unprocessed clauses: 575245
% 4.18/4.40  # ...number of literals in the above   : 1988042
% 4.18/4.40  # Current number of archived formulas  : 0
% 4.18/4.40  # Current number of archived clauses   : 1879
% 4.18/4.40  # Clause-clause subsumption calls (NU) : 514326
% 4.18/4.40  # Rec. Clause-clause subsumption calls : 498092
% 4.18/4.40  # Non-unit clause-clause subsumptions  : 30834
% 4.18/4.40  # Unit Clause-clause subsumption calls : 1893
% 4.18/4.40  # Rewrite failures with RHS unbound    : 0
% 4.18/4.40  # BW rewrite match attempts            : 1524
% 4.18/4.40  # BW rewrite match successes           : 352
% 4.18/4.40  # Condensation attempts                : 0
% 4.18/4.40  # Condensation successes               : 0
% 4.18/4.40  # Termbank termtop insertions          : 10675730
% 4.18/4.42  
% 4.18/4.42  # -------------------------------------------------
% 4.18/4.42  # User time                : 3.890 s
% 4.18/4.42  # System time              : 0.191 s
% 4.18/4.42  # Total time               : 4.081 s
% 4.18/4.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
