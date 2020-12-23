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
% DateTime   : Thu Dec  3 10:43:32 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 159 expanded)
%              Number of clauses        :   27 (  72 expanded)
%              Number of leaves         :    6 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 461 expanded)
%              Number of equality atoms :   37 ( 228 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X23)
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( X22 != X24
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( ~ r2_hidden(X22,X23)
        | X22 = X24
        | r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_8,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_11,plain,(
    ! [X16] : k4_xboole_0(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(esk2_2(X11,X12),X11)
        | ~ r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_15,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) )
      & ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) )
      & ( ~ r2_hidden(X18,X20)
        | ~ r2_hidden(X19,X21)
        | r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_22,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(X2,esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk4_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_xboole_0,esk3_0),esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_30,plain,
    ( k1_xboole_0 = X1
    | X2 = X3
    | r2_hidden(k4_tarski(esk2_2(X2,X3),esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X2,X1))
    | r2_hidden(esk2_2(X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk4_0 = X1
    | r2_hidden(esk2_2(esk4_0,X1),esk3_0)
    | r2_hidden(esk2_2(esk4_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk3_0)),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk4_0,esk3_0),esk2_2(k1_xboole_0,esk3_0)),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk4_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:07:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.20/0.41  # and selection function HSelectMinInfpos.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.41  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.20/0.41  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.41  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 0.20/0.41  fof(c_0_6, plain, ![X22, X23, X24]:(((r2_hidden(X22,X23)|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))&(X22!=X24|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24)))))&(~r2_hidden(X22,X23)|X22=X24|r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.41  fof(c_0_7, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  cnf(c_0_8, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_9, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_10, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.41  fof(c_0_11, plain, ![X16]:k4_xboole_0(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.41  cnf(c_0_12, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_13, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  fof(c_0_14, plain, ![X11, X12]:((~r2_hidden(esk2_2(X11,X12),X11)|~r2_hidden(esk2_2(X11,X12),X12)|X11=X12)&(r2_hidden(esk2_2(X11,X12),X11)|r2_hidden(esk2_2(X11,X12),X12)|X11=X12)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.20/0.41  fof(c_0_15, plain, ![X18, X19, X20, X21]:(((r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)))&(r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21))))&(~r2_hidden(X18,X20)|~r2_hidden(X19,X21)|r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.41  cnf(c_0_16, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.41  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 0.20/0.41  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_20, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.41  fof(c_0_21, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk3_0!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.41  cnf(c_0_22, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(X2,esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X3,X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk4_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(k1_xboole_0,esk3_0),esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk4_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_26])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 0.20/0.41  cnf(c_0_30, plain, (k1_xboole_0=X1|X2=X3|r2_hidden(k4_tarski(esk2_2(X2,X3),esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X2,X1))|r2_hidden(esk2_2(X2,X3),X3)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (esk4_0=X1|r2_hidden(esk2_2(esk4_0,X1),esk3_0)|r2_hidden(esk2_2(esk4_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk3_0)),k2_zfmisc_1(X2,esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_31])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_32]), c_0_33])).
% 0.20/0.41  cnf(c_0_36, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk4_0,esk3_0),esk2_2(k1_xboole_0,esk3_0)),k2_zfmisc_1(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_23])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk2_2(esk4_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_33])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_37]), c_0_38]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 40
% 0.20/0.41  # Proof object clause steps            : 27
% 0.20/0.41  # Proof object formula steps           : 13
% 0.20/0.41  # Proof object conjectures             : 17
% 0.20/0.41  # Proof object clause conjectures      : 14
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 11
% 0.20/0.41  # Proof object initial formulas used   : 6
% 0.20/0.41  # Proof object generating inferences   : 14
% 0.20/0.41  # Proof object simplifying inferences  : 9
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 8
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 20
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 19
% 0.20/0.41  # Processed clauses                    : 299
% 0.20/0.41  # ...of these trivial                  : 26
% 0.20/0.41  # ...subsumed                          : 41
% 0.20/0.41  # ...remaining for further processing  : 232
% 0.20/0.41  # Other redundant clauses eliminated   : 3
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 2539
% 0.20/0.41  # ...of the previous two non-trivial   : 2252
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 2520
% 0.20/0.41  # Factorizations                       : 16
% 0.20/0.41  # Equation resolutions                 : 3
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 211
% 0.20/0.41  #    Positive orientable unit clauses  : 86
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 6
% 0.20/0.41  #    Non-unit-clauses                  : 119
% 0.20/0.41  # Current number of unprocessed clauses: 1973
% 0.20/0.41  # ...number of literals in the above   : 4494
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 19
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1336
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1258
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 38
% 0.20/0.41  # Unit Clause-clause subsumption calls : 26
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 510
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 47853
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.065 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.070 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
