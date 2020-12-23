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
% DateTime   : Thu Dec  3 10:43:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 430 expanded)
%              Number of clauses        :   27 ( 198 expanded)
%              Number of leaves         :    4 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :   99 (1427 expanded)
%              Number of equality atoms :   22 ( 332 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t115_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X15)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_6,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk2_0) = k2_zfmisc_1(esk3_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk2_0) = k2_zfmisc_1(esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk3_0))
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk2_0 = X1
    | r2_hidden(esk1_2(X1,esk2_0),X1)
    | r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 = X1
    | esk2_0 = X2
    | r2_hidden(esk1_2(esk2_0,X1),esk3_0)
    | r2_hidden(esk1_2(X1,esk2_0),X1)
    | r2_hidden(esk1_2(X2,esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = X1
    | r2_hidden(esk1_2(esk3_0,esk2_0),esk3_0)
    | r2_hidden(esk1_2(X1,esk2_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_26]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk2_0),esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_30]),c_0_24])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(esk1_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:01:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DI
% 0.20/0.38  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t115_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X1)=k2_zfmisc_1(X2,X2)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 0.20/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X1)=k2_zfmisc_1(X2,X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t115_zfmisc_1])).
% 0.20/0.38  fof(c_0_5, plain, ![X13, X14, X15, X16]:(((r2_hidden(X13,X15)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))&(r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16))))&(~r2_hidden(X13,X15)|~r2_hidden(X14,X16)|r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_6, negated_conjecture, (k2_zfmisc_1(esk2_0,esk2_0)=k2_zfmisc_1(esk3_0,esk3_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.20/0.38  fof(c_0_7, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_10, negated_conjecture, (k2_zfmisc_1(esk2_0,esk2_0)=k2_zfmisc_1(esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk3_0))|~r2_hidden(X2,esk2_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.38  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk2_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.38  cnf(c_0_18, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 0.20/0.38  cnf(c_0_19, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_11, c_0_16])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (esk2_0=X1|r2_hidden(esk1_2(X1,esk2_0),X1)|r2_hidden(X2,esk3_0)|~r2_hidden(X2,esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_22, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_19, c_0_12])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (esk2_0=X1|esk2_0=X2|r2_hidden(esk1_2(esk2_0,X1),esk3_0)|r2_hidden(esk1_2(X1,esk2_0),X1)|r2_hidden(esk1_2(X2,esk2_0),X2)), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_21, c_0_10])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (esk2_0=X1|r2_hidden(esk1_2(esk3_0,esk2_0),esk3_0)|r2_hidden(esk1_2(X1,esk2_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_9])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_26]), c_0_24])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk2_0),esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_30])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_30]), c_0_24])).
% 0.20/0.38  cnf(c_0_33, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(esk1_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30])]), c_0_24]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 36
% 0.20/0.38  # Proof object clause steps            : 27
% 0.20/0.38  # Proof object formula steps           : 9
% 0.20/0.38  # Proof object conjectures             : 19
% 0.20/0.38  # Proof object clause conjectures      : 16
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 8
% 0.20/0.38  # Proof object initial formulas used   : 4
% 0.20/0.38  # Proof object generating inferences   : 19
% 0.20/0.38  # Proof object simplifying inferences  : 6
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 4
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 11
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 11
% 0.20/0.38  # Processed clauses                    : 80
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 21
% 0.20/0.38  # ...remaining for further processing  : 59
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 4
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 182
% 0.20/0.38  # ...of the previous two non-trivial   : 151
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 162
% 0.20/0.38  # Factorizations                       : 18
% 0.20/0.38  # Equation resolutions                 : 2
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
% 0.20/0.38  # Current number of processed clauses  : 42
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 35
% 0.20/0.38  # Current number of unprocessed clauses: 88
% 0.20/0.38  # ...number of literals in the above   : 423
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 15
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 286
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 203
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 23
% 0.20/0.38  # Unit Clause-clause subsumption calls : 10
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 2
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3822
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.035 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
