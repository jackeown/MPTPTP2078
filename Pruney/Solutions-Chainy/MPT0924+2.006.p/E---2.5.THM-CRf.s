%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 340 expanded)
%              Number of clauses        :   33 ( 151 expanded)
%              Number of leaves         :    6 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  104 ( 928 expanded)
%              Number of equality atoms :   14 ( 154 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
    <=> ( r2_hidden(X1,X5)
        & r2_hidden(X2,X6)
        & r2_hidden(X3,X7)
        & r2_hidden(X4,X8) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
      <=> ( r2_hidden(X1,X5)
          & r2_hidden(X2,X6)
          & r2_hidden(X3,X7)
          & r2_hidden(X4,X8) ) ) ),
    inference(assume_negation,[status(cth)],[t84_mcart_1])).

fof(c_0_7,plain,(
    ! [X19,X20,X21,X22] : k4_mcart_1(X19,X20,X21,X22) = k4_tarski(k3_mcart_1(X19,X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15] : k3_mcart_1(X13,X14,X15) = k4_tarski(k4_tarski(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X23,X24,X25,X26] : k4_zfmisc_1(X23,X24,X25,X26) = k2_zfmisc_1(k3_zfmisc_1(X23,X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X16,X17,X18] : k3_zfmisc_1(X16,X17,X18) = k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,negated_conjecture,
    ( ( ~ r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      | ~ r2_hidden(esk1_0,esk5_0)
      | ~ r2_hidden(esk2_0,esk6_0)
      | ~ r2_hidden(esk3_0,esk7_0)
      | ~ r2_hidden(esk4_0,esk8_0) )
    & ( r2_hidden(esk1_0,esk5_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk2_0,esk6_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk3_0,esk7_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk4_0,esk8_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_12,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X11)
        | ~ r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) )
      & ( r2_hidden(X10,X12)
        | ~ r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) )
      & ( ~ r2_hidden(X9,X11)
        | ~ r2_hidden(X10,X12)
        | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    | ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0)
    | ~ r2_hidden(esk4_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0)
    | ~ r2_hidden(esk4_0,esk8_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk1_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))
    | ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_18]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0) ),
    inference(csr,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))
    | ~ r2_hidden(esk2_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_18]),c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(esk3_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk2_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk7_0)
    | ~ r2_hidden(esk2_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_37]),c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_18]),c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(sr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_44]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t84_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))<=>(((r2_hidden(X1,X5)&r2_hidden(X2,X6))&r2_hidden(X3,X7))&r2_hidden(X4,X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_mcart_1)).
% 0.13/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.13/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.37  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))<=>(((r2_hidden(X1,X5)&r2_hidden(X2,X6))&r2_hidden(X3,X7))&r2_hidden(X4,X8)))), inference(assume_negation,[status(cth)],[t84_mcart_1])).
% 0.13/0.37  fof(c_0_7, plain, ![X19, X20, X21, X22]:k4_mcart_1(X19,X20,X21,X22)=k4_tarski(k3_mcart_1(X19,X20,X21),X22), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.13/0.37  fof(c_0_8, plain, ![X13, X14, X15]:k3_mcart_1(X13,X14,X15)=k4_tarski(k4_tarski(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.37  fof(c_0_9, plain, ![X23, X24, X25, X26]:k4_zfmisc_1(X23,X24,X25,X26)=k2_zfmisc_1(k3_zfmisc_1(X23,X24,X25),X26), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.13/0.37  fof(c_0_10, plain, ![X16, X17, X18]:k3_zfmisc_1(X16,X17,X18)=k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ((~r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))|(~r2_hidden(esk1_0,esk5_0)|~r2_hidden(esk2_0,esk6_0)|~r2_hidden(esk3_0,esk7_0)|~r2_hidden(esk4_0,esk8_0)))&((((r2_hidden(esk1_0,esk5_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)))&(r2_hidden(esk2_0,esk6_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))))&(r2_hidden(esk3_0,esk7_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))))&(r2_hidden(esk4_0,esk8_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.13/0.37  cnf(c_0_12, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_13, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_16, plain, ![X9, X10, X11, X12]:(((r2_hidden(X9,X11)|~r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)))&(r2_hidden(X10,X12)|~r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12))))&(~r2_hidden(X9,X11)|~r2_hidden(X10,X12)|r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(esk1_0,esk5_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_18, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (~r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))|~r2_hidden(esk1_0,esk5_0)|~r2_hidden(esk2_0,esk6_0)|~r2_hidden(esk3_0,esk7_0)|~r2_hidden(esk4_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk1_0,esk5_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk1_0,esk5_0)|~r2_hidden(esk2_0,esk6_0)|~r2_hidden(esk3_0,esk7_0)|~r2_hidden(esk4_0,esk8_0)|~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_19])).
% 0.13/0.37  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))|r2_hidden(esk1_0,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,esk8_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))|~r2_hidden(esk1_0,esk5_0)|~r2_hidden(esk2_0,esk6_0)|~r2_hidden(esk3_0,esk7_0)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_25]), c_0_21])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk4_0,esk8_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_18]), c_0_19])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))|~r2_hidden(esk2_0,esk6_0)|~r2_hidden(esk3_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])).
% 0.13/0.37  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,esk8_0)), inference(csr,[status(thm)],[c_0_29, c_0_24])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_0,esk6_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))|~r2_hidden(esk2_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_24])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_0,esk6_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_18]), c_0_19])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(esk3_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_31]), c_0_24])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))|r2_hidden(esk2_0,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_35])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_0,esk7_0)|r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk3_0,esk7_0)|~r2_hidden(esk2_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_28])])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_37]), c_0_24])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_0,esk7_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_18]), c_0_19])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk3_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(sr,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_21, c_0_43])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_44]), c_0_42]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 46
% 0.13/0.37  # Proof object clause steps            : 33
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 27
% 0.13/0.37  # Proof object clause conjectures      : 24
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 12
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 28
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 12
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 8
% 0.13/0.37  # Processed clauses                    : 29
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 28
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 9
% 0.13/0.37  # Generated clauses                    : 21
% 0.13/0.37  # ...of the previous two non-trivial   : 16
% 0.13/0.37  # Contextual simplify-reflections      : 6
% 0.13/0.37  # Paramodulations                      : 21
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 10
% 0.13/0.37  #    Positive orientable unit clauses  : 5
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 4
% 0.13/0.37  # Current number of unprocessed clauses: 1
% 0.13/0.37  # ...number of literals in the above   : 1
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 22
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 57
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 55
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.13/0.37  # Unit Clause-clause subsumption calls : 8
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1144
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
