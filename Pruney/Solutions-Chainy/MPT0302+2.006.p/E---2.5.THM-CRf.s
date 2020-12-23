%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:31 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 248 expanded)
%              Number of clauses        :   34 ( 110 expanded)
%              Number of leaves         :    6 (  61 expanded)
%              Depth                    :   20
%              Number of atoms          :   95 ( 677 expanded)
%              Number of equality atoms :   30 ( 293 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_16,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_hidden(X17,X19)
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)) )
      & ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)) )
      & ( ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X18,X20)
        | r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk4_0)),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk4_0)),k2_zfmisc_1(esk4_0,esk3_0))
    | r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk3_0
    | r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_32]),c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_34]),c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk3_0),esk2_1(esk3_0)),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_41]),c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk4_0)),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_42]),c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_45]),c_0_14]),c_0_41]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.19/0.43  # and selection function SelectSmallestOrientable.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.026 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.43  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 0.19/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.43  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.43  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.43  fof(c_0_6, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.43  fof(c_0_7, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.43  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 0.19/0.43  fof(c_0_9, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.43  cnf(c_0_10, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.43  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.43  fof(c_0_12, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk3_0!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.43  fof(c_0_13, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.43  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.43  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.43  fof(c_0_16, plain, ![X17, X18, X19, X20]:(((r2_hidden(X17,X19)|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)))&(r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20))))&(~r2_hidden(X17,X19)|~r2_hidden(X18,X20)|r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.43  cnf(c_0_17, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.43  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_21, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.43  cnf(c_0_22, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_23, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_19])).
% 0.19/0.43  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk4_0)),k2_zfmisc_1(X2,esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.43  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)|r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23])])).
% 0.19/0.43  cnf(c_0_26, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk4_0)),k2_zfmisc_1(esk4_0,esk3_0))|r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.19/0.43  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.43  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)|r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.43  cnf(c_0_31, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_1(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 0.19/0.43  cnf(c_0_34, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk3_0|r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_32]), c_0_14])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_33])).
% 0.19/0.43  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_34]), c_0_22])).
% 0.19/0.43  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk3_0),esk2_1(esk3_0)),k2_zfmisc_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.43  cnf(c_0_40, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_39])).
% 0.19/0.43  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_10, c_0_40])).
% 0.19/0.43  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_41]), c_0_22])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk4_0)),k2_zfmisc_1(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_42]), c_0_26])).
% 0.19/0.43  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 0.19/0.43  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 0.19/0.43  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_45]), c_0_14]), c_0_41]), c_0_22]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 47
% 0.19/0.43  # Proof object clause steps            : 34
% 0.19/0.43  # Proof object formula steps           : 13
% 0.19/0.43  # Proof object conjectures             : 27
% 0.19/0.43  # Proof object clause conjectures      : 24
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 11
% 0.19/0.43  # Proof object initial formulas used   : 6
% 0.19/0.43  # Proof object generating inferences   : 23
% 0.19/0.43  # Proof object simplifying inferences  : 9
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 6
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 13
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 13
% 0.19/0.43  # Processed clauses                    : 258
% 0.19/0.43  # ...of these trivial                  : 5
% 0.19/0.43  # ...subsumed                          : 45
% 0.19/0.43  # ...remaining for further processing  : 208
% 0.19/0.43  # Other redundant clauses eliminated   : 6
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 0
% 0.19/0.43  # Backward-rewritten                   : 7
% 0.19/0.43  # Generated clauses                    : 6480
% 0.19/0.43  # ...of the previous two non-trivial   : 5327
% 0.19/0.43  # Contextual simplify-reflections      : 0
% 0.19/0.43  # Paramodulations                      : 6474
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 6
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 188
% 0.19/0.43  #    Positive orientable unit clauses  : 35
% 0.19/0.43  #    Positive unorientable unit clauses: 1
% 0.19/0.43  #    Negative unit clauses             : 3
% 0.19/0.43  #    Non-unit-clauses                  : 149
% 0.19/0.43  # Current number of unprocessed clauses: 5091
% 0.19/0.43  # ...number of literals in the above   : 14257
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 20
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 1505
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 1262
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 44
% 0.19/0.43  # Unit Clause-clause subsumption calls : 339
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 49
% 0.19/0.43  # BW rewrite match successes           : 4
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 104473
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.086 s
% 0.19/0.43  # System time              : 0.008 s
% 0.19/0.43  # Total time               : 0.094 s
% 0.19/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
