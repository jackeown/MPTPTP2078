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
% DateTime   : Thu Dec  3 10:43:36 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 124 expanded)
%              Number of clauses        :   22 (  57 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 375 expanded)
%              Number of equality atoms :   12 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t115_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r2_hidden(X16,X18)
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)) )
      & ( r2_hidden(X17,X19)
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)) )
      & ( ~ r2_hidden(X16,X18)
        | ~ r2_hidden(X17,X19)
        | r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk3_0) = k2_zfmisc_1(esk4_0,esk4_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk3_0) = k2_zfmisc_1(esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))
    | r1_tarski(X2,X3)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X3,X4)),k2_zfmisc_1(X1,X3))
    | r1_tarski(X1,X2)
    | r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1)
    | r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | ~ r2_xboole_0(X11,X12) )
      & ( X11 != X12
        | ~ r2_xboole_0(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | X11 = X12
        | r2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ( r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X13)
        | ~ r2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(ef,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_2(esk4_0,esk3_0)),k2_zfmisc_1(X2,esk3_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_26])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk4_0,esk3_0),esk2_2(esk4_0,esk3_0)),k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_12])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:25:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.14/0.38  # and selection function SelectNewComplexAHPNS.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t115_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X1)=k2_zfmisc_1(X2,X2)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 0.14/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.14/0.38  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X1)=k2_zfmisc_1(X2,X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t115_zfmisc_1])).
% 0.14/0.38  fof(c_0_6, plain, ![X16, X17, X18, X19]:(((r2_hidden(X16,X18)|~r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)))&(r2_hidden(X17,X19)|~r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19))))&(~r2_hidden(X16,X18)|~r2_hidden(X17,X19)|r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, (k2_zfmisc_1(esk3_0,esk3_0)=k2_zfmisc_1(esk4_0,esk4_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.38  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (k2_zfmisc_1(esk3_0,esk3_0)=k2_zfmisc_1(esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))|r1_tarski(X2,X3)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X3,X4)),k2_zfmisc_1(X1,X3))|r1_tarski(X1,X2)|r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_13, c_0_10])).
% 0.14/0.38  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)|r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.38  fof(c_0_18, plain, ![X11, X12]:(((r1_tarski(X11,X12)|~r2_xboole_0(X11,X12))&(X11!=X12|~r2_xboole_0(X11,X12)))&(~r1_tarski(X11,X12)|X11=X12|r2_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  fof(c_0_20, plain, ![X13, X14]:((r2_hidden(esk2_2(X13,X14),X14)|~r2_xboole_0(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X13)|~r2_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.14/0.38  cnf(c_0_21, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(ef,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r2_xboole_0(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_2(esk4_0,esk3_0)),k2_zfmisc_1(X2,esk3_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_26])).
% 0.14/0.38  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk4_0,esk3_0),esk2_2(esk4_0,esk3_0)),k2_zfmisc_1(esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_12])).
% 0.14/0.38  cnf(c_0_30, plain, (~r2_hidden(esk2_2(X1,X2),X1)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_25])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 33
% 0.14/0.38  # Proof object clause steps            : 22
% 0.14/0.38  # Proof object formula steps           : 11
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 10
% 0.14/0.38  # Proof object initial formulas used   : 5
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 4
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 5
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 13
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 13
% 0.14/0.38  # Processed clauses                    : 30
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 30
% 0.14/0.38  # Other redundant clauses eliminated   : 1
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 58
% 0.14/0.38  # ...of the previous two non-trivial   : 51
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 55
% 0.14/0.38  # Factorizations                       : 2
% 0.14/0.38  # Equation resolutions                 : 1
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 27
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 18
% 0.14/0.38  # Current number of unprocessed clauses: 25
% 0.14/0.38  # ...number of literals in the above   : 77
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 2
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 45
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 36
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 8
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 3
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1523
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.027 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
