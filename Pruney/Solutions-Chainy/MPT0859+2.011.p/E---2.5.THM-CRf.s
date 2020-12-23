%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:09 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 183 expanded)
%              Number of clauses        :   22 (  82 expanded)
%              Number of leaves         :    5 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 466 expanded)
%              Number of equality atoms :   46 ( 239 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t15_mcart_1])).

fof(c_0_6,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,k2_zfmisc_1(X16,X17))
      | k4_tarski(esk2_1(X15),esk3_1(X15)) = X15 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

fof(c_0_7,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(k2_tarski(esk5_0,esk6_0),esk7_0))
    & ( k1_mcart_1(esk4_0) != esk5_0
      | ~ r2_hidden(k2_mcart_1(esk4_0),esk7_0) )
    & ( k1_mcart_1(esk4_0) != esk6_0
      | ~ r2_hidden(k2_mcart_1(esk4_0),esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X24,X25] :
      ( k1_mcart_1(k4_tarski(X24,X25)) = X24
      & k2_mcart_1(k4_tarski(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_9,plain,
    ( k4_tarski(esk2_1(X1),esk3_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(k2_tarski(esk5_0,esk6_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k4_tarski(esk2_1(esk4_0),esk3_1(esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( esk2_1(esk4_0) = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_14,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),esk3_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X21,X23)
        | r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_17,negated_conjecture,
    ( esk3_1(esk4_0) = k2_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_17])).

fof(c_0_20,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk4_0),X1)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk4_0),X1)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k1_mcart_1(esk4_0) != esk5_0
    | ~ r2_hidden(k2_mcart_1(esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk4_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( k1_mcart_1(esk4_0) != esk6_0
    | ~ r2_hidden(k2_mcart_1(esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( k1_mcart_1(esk4_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( k1_mcart_1(esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:01:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03FN
% 0.12/0.37  # and selection function PSelectLComplex.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t15_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 0.12/0.37  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.12/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.37  fof(t106_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 0.12/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4)))), inference(assume_negation,[status(cth)],[t15_mcart_1])).
% 0.12/0.37  fof(c_0_6, plain, ![X15, X16, X17]:(~r2_hidden(X15,k2_zfmisc_1(X16,X17))|k4_tarski(esk2_1(X15),esk3_1(X15))=X15), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.12/0.37  fof(c_0_7, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(k2_tarski(esk5_0,esk6_0),esk7_0))&((k1_mcart_1(esk4_0)!=esk5_0|~r2_hidden(k2_mcart_1(esk4_0),esk7_0))&(k1_mcart_1(esk4_0)!=esk6_0|~r2_hidden(k2_mcart_1(esk4_0),esk7_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X24, X25]:(k1_mcart_1(k4_tarski(X24,X25))=X24&k2_mcart_1(k4_tarski(X24,X25))=X25), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.37  cnf(c_0_9, plain, (k4_tarski(esk2_1(X1),esk3_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(k2_tarski(esk5_0,esk6_0),esk7_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (k4_tarski(esk2_1(esk4_0),esk3_1(esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (esk2_1(esk4_0)=k1_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.37  cnf(c_0_14, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),esk3_1(esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.37  fof(c_0_16, plain, ![X20, X21, X22, X23]:(((r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))&(r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23))))&(~r2_hidden(X20,X22)|~r2_hidden(X21,X23)|r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (esk3_1(esk4_0)=k2_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_15, c_0_17])).
% 0.12/0.37  fof(c_0_20, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(k2_mcart_1(esk4_0),X1)|~r2_hidden(esk4_0,k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_23, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(k1_mcart_1(esk4_0),X1)|~r2_hidden(esk4_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (k1_mcart_1(esk4_0)!=esk5_0|~r2_hidden(k2_mcart_1(esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(k2_mcart_1(esk4_0),esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_10])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (k1_mcart_1(esk4_0)!=esk6_0|~r2_hidden(k2_mcart_1(esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_28, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(k1_mcart_1(esk4_0),k2_tarski(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_10])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k1_mcart_1(esk4_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (k1_mcart_1(esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26])])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 33
% 0.12/0.37  # Proof object clause steps            : 22
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 18
% 0.12/0.37  # Proof object clause conjectures      : 15
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 9
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 15
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 15
% 0.12/0.37  # Processed clauses                    : 48
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 3
% 0.12/0.37  # ...remaining for further processing  : 45
% 0.12/0.37  # Other redundant clauses eliminated   : 7
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 4
% 0.12/0.37  # Generated clauses                    : 42
% 0.12/0.37  # ...of the previous two non-trivial   : 37
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 29
% 0.12/0.37  # Factorizations                       : 8
% 0.12/0.37  # Equation resolutions                 : 7
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 23
% 0.12/0.37  #    Positive orientable unit clauses  : 10
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 11
% 0.12/0.37  # Current number of unprocessed clauses: 13
% 0.12/0.37  # ...number of literals in the above   : 39
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 19
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 17
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 17
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.37  # Unit Clause-clause subsumption calls : 16
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 3
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1369
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.028 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.032 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
