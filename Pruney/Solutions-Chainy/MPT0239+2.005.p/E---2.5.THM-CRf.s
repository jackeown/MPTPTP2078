%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:27 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 202 expanded)
%              Number of clauses        :   23 (  94 expanded)
%              Number of leaves         :    4 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 545 expanded)
%              Number of equality atoms :   45 ( 308 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
      <=> ( X1 = X3
          & X2 = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t34_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X38
        | X39 != k1_tarski(X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k1_tarski(X38) )
      & ( ~ r2_hidden(esk6_2(X42,X43),X43)
        | esk6_2(X42,X43) != X42
        | X43 = k1_tarski(X42) )
      & ( r2_hidden(esk6_2(X42,X43),X43)
        | esk6_2(X42,X43) = X42
        | X43 = k1_tarski(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X50] : k2_enumset1(X50,X50,X50,X50) = k1_tarski(X50) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_7,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0)))
      | esk7_0 != esk9_0
      | esk8_0 != esk10_0 )
    & ( esk7_0 = esk9_0
      | r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0))) )
    & ( esk8_0 = esk10_0
      | r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X56,X57,X58,X59] :
      ( ( r2_hidden(X56,X58)
        | ~ r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(X58,X59)) )
      & ( r2_hidden(X57,X59)
        | ~ r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(X58,X59)) )
      & ( ~ r2_hidden(X56,X58)
        | ~ r2_hidden(X57,X59)
        | r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(X58,X59)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_11,negated_conjecture,
    ( esk8_0 = esk10_0
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( esk7_0 = esk9_0
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0)))
    | esk7_0 != esk9_0
    | esk8_0 != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( esk10_0 = esk8_0
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_9]),c_0_9])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( esk9_0 = esk7_0
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_9]),c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( esk9_0 != esk7_0
    | esk10_0 != esk8_0
    | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_9]),c_0_9])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( esk10_0 = esk8_0
    | r2_hidden(esk8_0,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( esk7_0 = esk9_0
    | r2_hidden(esk7_0,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( esk7_0 != esk9_0
    | esk10_0 != esk8_0
    | ~ r2_hidden(esk8_0,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))
    | ~ r2_hidden(esk7_0,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk10_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( esk7_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29])]),c_0_30]),c_0_30]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.029 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t34_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 0.14/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.14/0.37  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.14/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.14/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4))), inference(assume_negation,[status(cth)],[t34_zfmisc_1])).
% 0.14/0.37  fof(c_0_5, plain, ![X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X40,X39)|X40=X38|X39!=k1_tarski(X38))&(X41!=X38|r2_hidden(X41,X39)|X39!=k1_tarski(X38)))&((~r2_hidden(esk6_2(X42,X43),X43)|esk6_2(X42,X43)!=X42|X43=k1_tarski(X42))&(r2_hidden(esk6_2(X42,X43),X43)|esk6_2(X42,X43)=X42|X43=k1_tarski(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.14/0.37  fof(c_0_6, plain, ![X50]:k2_enumset1(X50,X50,X50,X50)=k1_tarski(X50), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.14/0.37  fof(c_0_7, negated_conjecture, ((~r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0)))|(esk7_0!=esk9_0|esk8_0!=esk10_0))&((esk7_0=esk9_0|r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0))))&(esk8_0=esk10_0|r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.14/0.37  cnf(c_0_8, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_9, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  fof(c_0_10, plain, ![X56, X57, X58, X59]:(((r2_hidden(X56,X58)|~r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(X58,X59)))&(r2_hidden(X57,X59)|~r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(X58,X59))))&(~r2_hidden(X56,X58)|~r2_hidden(X57,X59)|r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(X58,X59)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.14/0.37  cnf(c_0_11, negated_conjecture, (esk8_0=esk10_0|r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (esk7_0=esk9_0|r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (~r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k1_tarski(esk9_0),k1_tarski(esk10_0)))|esk7_0!=esk9_0|esk8_0!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_15, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.37  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (esk10_0=esk8_0|r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_9]), c_0_9])).
% 0.14/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[c_0_12, c_0_9])).
% 0.14/0.37  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (esk9_0=esk7_0|r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_9]), c_0_9])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (esk9_0!=esk7_0|esk10_0!=esk8_0|~r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_9]), c_0_9])).
% 0.14/0.37  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_23, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (esk10_0=esk8_0|r2_hidden(esk8_0,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.37  cnf(c_0_25, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (esk7_0=esk9_0|r2_hidden(esk7_0,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (esk7_0!=esk9_0|esk10_0!=esk8_0|~r2_hidden(esk8_0,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))|~r2_hidden(esk7_0,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (esk10_0=esk8_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.37  cnf(c_0_29, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, (esk7_0=esk9_0), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29])]), c_0_30]), c_0_30]), c_0_29])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 32
% 0.14/0.37  # Proof object clause steps            : 23
% 0.14/0.37  # Proof object formula steps           : 9
% 0.14/0.37  # Proof object conjectures             : 15
% 0.14/0.37  # Proof object clause conjectures      : 12
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 9
% 0.14/0.37  # Proof object initial formulas used   : 4
% 0.14/0.37  # Proof object generating inferences   : 7
% 0.14/0.37  # Proof object simplifying inferences  : 20
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 13
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 34
% 0.14/0.37  # Removed in clause preprocessing      : 2
% 0.14/0.37  # Initial clauses in saturation        : 32
% 0.14/0.37  # Processed clauses                    : 85
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 11
% 0.14/0.37  # ...remaining for further processing  : 73
% 0.14/0.37  # Other redundant clauses eliminated   : 1
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 1
% 0.14/0.37  # Backward-rewritten                   : 7
% 0.14/0.37  # Generated clauses                    : 57
% 0.14/0.37  # ...of the previous two non-trivial   : 48
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 49
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 8
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 32
% 0.14/0.37  #    Positive orientable unit clauses  : 4
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 0
% 0.14/0.37  #    Non-unit-clauses                  : 28
% 0.14/0.37  # Current number of unprocessed clauses: 27
% 0.14/0.37  # ...number of literals in the above   : 70
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 42
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 410
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 233
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 11
% 0.14/0.37  # Unit Clause-clause subsumption calls : 14
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 4
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3217
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.033 s
% 0.14/0.37  # System time              : 0.003 s
% 0.14/0.37  # Total time               : 0.037 s
% 0.14/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
