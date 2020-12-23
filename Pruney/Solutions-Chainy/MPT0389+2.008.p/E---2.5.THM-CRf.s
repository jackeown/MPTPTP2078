%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:05 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 130 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ( X1 = k1_xboole_0
          | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t7_setfam_1])).

fof(c_0_7,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & esk2_0 != k1_xboole_0
    & ~ r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X13,X14] :
      ( ( r2_hidden(esk1_2(X13,X14),X13)
        | X13 = k1_xboole_0
        | r1_tarski(X14,k1_setfam_1(X13)) )
      & ( ~ r1_tarski(X14,esk1_2(X13,X14))
        | X13 = k1_xboole_0
        | r1_tarski(X14,k1_setfam_1(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(k1_tarski(X9),X10) != k1_xboole_0
        | r2_hidden(X9,X10) )
      & ( ~ r2_hidden(X9,X10)
        | k4_xboole_0(k1_tarski(X9),X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_10,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ( k4_xboole_0(X4,X5) != k1_xboole_0
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | k4_xboole_0(X4,X5) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,X1),esk2_0)
    | r1_tarski(X1,k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_2(esk2_0,X1)),esk2_0) = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k1_tarski(esk1_2(esk2_0,X1)),esk2_0)
    | r1_tarski(X1,k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k1_tarski(esk1_2(esk2_0,X1)),esk3_0)
    | r1_tarski(X1,k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | r1_tarski(k1_setfam_1(X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_2(esk2_0,X1)),esk3_0) = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,X1),esk3_0)
    | r1_tarski(X1,k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk1_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk3_0),esk1_2(esk2_0,X1))
    | r1_tarski(X1,k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_10]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.20/0.39  # and selection function SelectSmallestOrientable.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t7_setfam_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.20/0.39  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.20/0.39  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.20/0.39  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.39  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.39  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))))), inference(assume_negation,[status(cth)],[t7_setfam_1])).
% 0.20/0.39  fof(c_0_7, negated_conjecture, (r1_tarski(esk2_0,esk3_0)&(esk2_0!=k1_xboole_0&~r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.39  fof(c_0_8, plain, ![X13, X14]:((r2_hidden(esk1_2(X13,X14),X13)|(X13=k1_xboole_0|r1_tarski(X14,k1_setfam_1(X13))))&(~r1_tarski(X14,esk1_2(X13,X14))|(X13=k1_xboole_0|r1_tarski(X14,k1_setfam_1(X13))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.20/0.39  fof(c_0_9, plain, ![X9, X10]:((k4_xboole_0(k1_tarski(X9),X10)!=k1_xboole_0|r2_hidden(X9,X10))&(~r2_hidden(X9,X10)|k4_xboole_0(k1_tarski(X9),X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.20/0.39  cnf(c_0_10, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  fof(c_0_12, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.39  fof(c_0_13, plain, ![X4, X5]:((k4_xboole_0(X4,X5)!=k1_xboole_0|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|k4_xboole_0(X4,X5)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.39  cnf(c_0_14, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_2(esk2_0,X1),esk2_0)|r1_tarski(X1,k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.39  cnf(c_0_16, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_18, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_2(esk2_0,X1)),esk2_0)=k1_xboole_0|r1_tarski(X1,k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (r1_tarski(k1_tarski(esk1_2(esk2_0,X1)),esk2_0)|r1_tarski(X1,k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (r1_tarski(k1_tarski(esk1_2(esk2_0,X1)),esk3_0)|r1_tarski(X1,k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  fof(c_0_24, plain, ![X11, X12]:(~r2_hidden(X11,X12)|r1_tarski(k1_setfam_1(X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.39  cnf(c_0_25, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_2(esk2_0,X1)),esk3_0)=k1_xboole_0|r1_tarski(X1,k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  cnf(c_0_27, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(esk2_0,X1),esk3_0)|r1_tarski(X1,k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  cnf(c_0_29, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk1_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (r1_tarski(k1_setfam_1(esk3_0),esk1_2(esk2_0,X1))|r1_tarski(X1,k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (~r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_10]), c_0_31]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 33
% 0.20/0.39  # Proof object clause steps            : 20
% 0.20/0.39  # Proof object formula steps           : 13
% 0.20/0.39  # Proof object conjectures             : 15
% 0.20/0.39  # Proof object clause conjectures      : 12
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 11
% 0.20/0.39  # Proof object initial formulas used   : 6
% 0.20/0.39  # Proof object generating inferences   : 9
% 0.20/0.39  # Proof object simplifying inferences  : 2
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 6
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 11
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 11
% 0.20/0.39  # Processed clauses                    : 56
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 7
% 0.20/0.39  # ...remaining for further processing  : 49
% 0.20/0.39  # Other redundant clauses eliminated   : 6
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 2
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 345
% 0.20/0.39  # ...of the previous two non-trivial   : 322
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 339
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 6
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 36
% 0.20/0.39  #    Positive orientable unit clauses  : 4
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 30
% 0.20/0.39  # Current number of unprocessed clauses: 285
% 0.20/0.39  # ...number of literals in the above   : 1557
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 13
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 87
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 64
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.20/0.39  # Unit Clause-clause subsumption calls : 1
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 6237
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.037 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.043 s
% 0.20/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
