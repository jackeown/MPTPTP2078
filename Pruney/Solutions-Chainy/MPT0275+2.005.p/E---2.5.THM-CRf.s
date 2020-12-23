%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 103 expanded)
%              Number of clauses        :   24 (  48 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 248 expanded)
%              Number of equality atoms :   21 (  87 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

fof(c_0_5,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) != k1_xboole_0
      | ~ r2_hidden(esk2_0,esk4_0)
      | ~ r2_hidden(esk3_0,esk4_0) )
    & ( r2_hidden(esk2_0,esk4_0)
      | k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_xboole_0 )
    & ( r2_hidden(esk3_0,esk4_0)
      | k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X28,X29] : k2_tarski(X28,X29) = k2_xboole_0(k1_tarski(X28),k1_tarski(X29)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_7,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(X34,X36)
        | ~ r1_tarski(k2_tarski(X34,X35),X36) )
      & ( r2_hidden(X35,X36)
        | ~ r1_tarski(k2_tarski(X34,X35),X36) )
      & ( ~ r2_hidden(X34,X36)
        | ~ r2_hidden(X35,X36)
        | r1_tarski(k2_tarski(X34,X35),X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) = k1_xboole_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X3),k1_tarski(X1)),X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) = k1_xboole_0
    | r2_hidden(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) != k1_xboole_0
    | ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(X3)),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(X3)),X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) != k1_xboole_0
    | ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(esk3_0)),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) != k1_xboole_0
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:02:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.20/0.38  # and selection function SelectCQIPrecW.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 0.20/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.38  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.38  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.20/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ((k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)!=k1_xboole_0|(~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)))&((r2_hidden(esk2_0,esk4_0)|k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_xboole_0)&(r2_hidden(esk3_0,esk4_0)|k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.20/0.38  fof(c_0_6, plain, ![X28, X29]:k2_tarski(X28,X29)=k2_xboole_0(k1_tarski(X28),k1_tarski(X29)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.38  fof(c_0_7, plain, ![X34, X35, X36]:(((r2_hidden(X34,X36)|~r1_tarski(k2_tarski(X34,X35),X36))&(r2_hidden(X35,X36)|~r1_tarski(k2_tarski(X34,X35),X36)))&(~r2_hidden(X34,X36)|~r2_hidden(X35,X36)|r1_tarski(k2_tarski(X34,X35),X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.20/0.38  cnf(c_0_9, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_10, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)=k1_xboole_0|r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_15, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_tarski(X3),k1_tarski(X1)),X2)), inference(rw,[status(thm)],[c_0_11, c_0_10])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)=k1_xboole_0|r2_hidden(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_14, c_0_10])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (k4_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)!=k1_xboole_0|~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_21, plain, (r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(X3)),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_10])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(X3)),X2)), inference(rw,[status(thm)],[c_0_18, c_0_10])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)!=k1_xboole_0|~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_20, c_0_10])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(esk3_0)),esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)!=k1_xboole_0|~r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22])])).
% 0.20/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_27])])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 33
% 0.20/0.38  # Proof object clause steps            : 24
% 0.20/0.38  # Proof object formula steps           : 9
% 0.20/0.38  # Proof object conjectures             : 18
% 0.20/0.38  # Proof object clause conjectures      : 15
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 9
% 0.20/0.38  # Proof object initial formulas used   : 4
% 0.20/0.38  # Proof object generating inferences   : 7
% 0.20/0.38  # Proof object simplifying inferences  : 11
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 20
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 35
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 33
% 0.20/0.38  # Processed clauses                    : 168
% 0.20/0.38  # ...of these trivial                  : 7
% 0.20/0.38  # ...subsumed                          : 42
% 0.20/0.38  # ...remaining for further processing  : 119
% 0.20/0.38  # Other redundant clauses eliminated   : 8
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 19
% 0.20/0.38  # Generated clauses                    : 218
% 0.20/0.38  # ...of the previous two non-trivial   : 152
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 211
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 8
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
% 0.20/0.38  # Current number of processed clauses  : 63
% 0.20/0.38  #    Positive orientable unit clauses  : 27
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 5
% 0.20/0.38  #    Non-unit-clauses                  : 30
% 0.20/0.38  # Current number of unprocessed clauses: 50
% 0.20/0.38  # ...number of literals in the above   : 97
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 55
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 517
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 487
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 21
% 0.20/0.38  # Unit Clause-clause subsumption calls : 127
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 63
% 0.20/0.38  # BW rewrite match successes           : 26
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3870
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
