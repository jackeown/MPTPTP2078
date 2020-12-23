%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:33 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 201 expanded)
%              Number of clauses        :   30 (  87 expanded)
%              Number of leaves         :    5 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :   95 ( 648 expanded)
%              Number of equality atoms :   26 ( 258 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

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

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

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
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)) )
      & ( r2_hidden(X16,X18)
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)) )
      & ( ~ r2_hidden(X15,X17)
        | ~ r2_hidden(X16,X18)
        | r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk3_0),esk2_1(esk3_0)),k2_zfmisc_1(esk3_0,esk4_0))
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk4_0)),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_29]),c_0_18]),c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk4_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_35]),c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk3_0),esk2_1(esk3_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_36]),c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_35]),c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.20/0.43  # and selection function SelectSmallestOrientable.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.026 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.43  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.44  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 0.20/0.44  fof(c_0_6, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.44  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.44  fof(c_0_8, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk3_0!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.44  fof(c_0_9, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.44  cnf(c_0_10, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.44  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.44  fof(c_0_12, plain, ![X15, X16, X17, X18]:(((r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)))&(r2_hidden(X16,X18)|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18))))&(~r2_hidden(X15,X17)|~r2_hidden(X16,X18)|r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.44  cnf(c_0_13, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_14, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_15, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.44  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.44  cnf(c_0_17, negated_conjecture, (r2_hidden(esk2_1(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.44  cnf(c_0_18, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_19, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_11])).
% 0.20/0.44  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.44  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)|r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19])])).
% 0.20/0.44  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.44  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk3_0),esk2_1(esk3_0)),k2_zfmisc_1(esk3_0,esk4_0))|r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.44  cnf(c_0_25, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.44  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)|r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.44  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_14])).
% 0.20/0.44  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)|r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.44  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk4_0)),k2_zfmisc_1(X2,esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_28])).
% 0.20/0.44  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_29]), c_0_18]), c_0_11])).
% 0.20/0.44  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.20/0.44  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk4_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.44  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.44  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_34])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_35]), c_0_18])).
% 0.20/0.44  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk3_0),esk2_1(esk3_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_36]), c_0_22])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_37])).
% 0.20/0.44  cnf(c_0_39, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_35]), c_0_18])).
% 0.20/0.44  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_38]), c_0_39]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 41
% 0.20/0.44  # Proof object clause steps            : 30
% 0.20/0.44  # Proof object formula steps           : 11
% 0.20/0.44  # Proof object conjectures             : 25
% 0.20/0.44  # Proof object clause conjectures      : 22
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 10
% 0.20/0.44  # Proof object initial formulas used   : 5
% 0.20/0.44  # Proof object generating inferences   : 20
% 0.20/0.44  # Proof object simplifying inferences  : 8
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 5
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 14
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 14
% 0.20/0.44  # Processed clauses                    : 256
% 0.20/0.44  # ...of these trivial                  : 5
% 0.20/0.44  # ...subsumed                          : 52
% 0.20/0.44  # ...remaining for further processing  : 199
% 0.20/0.44  # Other redundant clauses eliminated   : 8
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 0
% 0.20/0.44  # Backward-rewritten                   : 8
% 0.20/0.44  # Generated clauses                    : 5867
% 0.20/0.44  # ...of the previous two non-trivial   : 4764
% 0.20/0.44  # Contextual simplify-reflections      : 1
% 0.20/0.44  # Paramodulations                      : 5855
% 0.20/0.44  # Factorizations                       : 4
% 0.20/0.44  # Equation resolutions                 : 8
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 176
% 0.20/0.44  #    Positive orientable unit clauses  : 35
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 4
% 0.20/0.44  #    Non-unit-clauses                  : 137
% 0.20/0.44  # Current number of unprocessed clauses: 4500
% 0.20/0.44  # ...number of literals in the above   : 12793
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 21
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 1072
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 898
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 52
% 0.20/0.44  # Unit Clause-clause subsumption calls : 44
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 42
% 0.20/0.44  # BW rewrite match successes           : 3
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 92357
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.081 s
% 0.20/0.44  # System time              : 0.009 s
% 0.20/0.44  # Total time               : 0.090 s
% 0.20/0.44  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
