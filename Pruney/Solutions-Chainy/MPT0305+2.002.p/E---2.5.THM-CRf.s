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
% DateTime   : Thu Dec  3 10:43:36 EST 2020

% Result     : Theorem 15.11s
% Output     : CNFRefutation 15.11s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 172 expanded)
%              Number of clauses        :   35 (  81 expanded)
%              Number of leaves         :    5 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  134 ( 608 expanded)
%              Number of equality atoms :   33 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t117_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
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

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X15)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
            | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
          & ~ r1_tarski(X2,X3) ) ),
    inference(assume_negation,[status(cth)],[t117_zfmisc_1])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_16,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    & ( r1_tarski(k2_zfmisc_1(esk3_0,esk2_0),k2_zfmisc_1(esk4_0,esk2_0))
      | r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) )
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(esk1_2(k1_xboole_0,X1),X2),k1_xboole_0)
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(esk1_2(k1_xboole_0,X1),esk1_2(esk3_0,esk4_0)),k1_xboole_0)
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X5)
    | ~ r1_tarski(k2_zfmisc_1(X5,X4),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk2_0),k2_zfmisc_1(esk4_0,esk2_0))
    | r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1)
    | r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk2_0))
    | r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))
    | r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))
    | r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk2_0,esk4_0))
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))
    | r2_hidden(k4_tarski(X1,esk1_2(esk3_0,esk4_0)),k2_zfmisc_1(esk2_0,esk4_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk2_0,k1_xboole_0),esk1_2(esk3_0,esk4_0)),k2_zfmisc_1(esk2_0,esk4_0))
    | r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_35]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk2_0,k1_xboole_0),esk1_2(esk3_0,esk4_0)),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_41]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:06:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 15.11/15.30  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DI
% 15.11/15.30  # and selection function PSelectComplexExceptRRHorn.
% 15.11/15.30  #
% 15.11/15.30  # Preprocessing time       : 0.027 s
% 15.11/15.30  # Presaturation interreduction done
% 15.11/15.30  
% 15.11/15.30  # Proof found!
% 15.11/15.30  # SZS status Theorem
% 15.11/15.30  # SZS output start CNFRefutation
% 15.11/15.30  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.11/15.30  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.11/15.30  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.11/15.30  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 15.11/15.30  fof(t117_zfmisc_1, conjecture, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 15.11/15.30  fof(c_0_5, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 15.11/15.30  fof(c_0_6, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 15.11/15.30  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 15.11/15.30  fof(c_0_8, plain, ![X13, X14, X15, X16]:(((r2_hidden(X13,X15)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))&(r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16))))&(~r2_hidden(X13,X15)|~r2_hidden(X14,X16)|r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 15.11/15.30  cnf(c_0_9, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 15.11/15.30  cnf(c_0_10, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 15.11/15.30  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 15.11/15.30  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t117_zfmisc_1])).
% 15.11/15.30  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 15.11/15.30  cnf(c_0_14, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 15.11/15.30  cnf(c_0_15, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 15.11/15.30  fof(c_0_16, negated_conjecture, ((esk2_0!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(esk3_0,esk2_0),k2_zfmisc_1(esk4_0,esk2_0))|r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))))&~r1_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 15.11/15.30  cnf(c_0_17, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 15.11/15.30  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X2),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 15.11/15.30  cnf(c_0_19, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_15, c_0_11])).
% 15.11/15.30  cnf(c_0_20, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 15.11/15.30  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 15.11/15.30  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 15.11/15.30  cnf(c_0_23, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 15.11/15.30  cnf(c_0_24, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(esk1_2(k1_xboole_0,X1),X2),k1_xboole_0)|r2_hidden(esk1_2(X1,k1_xboole_0),X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 15.11/15.30  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_11])).
% 15.11/15.30  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 15.11/15.30  cnf(c_0_27, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_10, c_0_21])).
% 15.11/15.30  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 15.11/15.30  cnf(c_0_29, negated_conjecture, (k1_xboole_0=X1|r2_hidden(k4_tarski(esk1_2(k1_xboole_0,X1),esk1_2(esk3_0,esk4_0)),k1_xboole_0)|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 15.11/15.30  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|~r2_hidden(X1,X5)|~r1_tarski(k2_zfmisc_1(X5,X4),X3)), inference(spm,[status(thm)],[c_0_26, c_0_13])).
% 15.11/15.30  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk2_0),k2_zfmisc_1(esk4_0,esk2_0))|r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 15.11/15.30  cnf(c_0_32, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_11])).
% 15.11/15.30  cnf(c_0_33, negated_conjecture, (k1_xboole_0=X1|r2_hidden(esk1_2(X1,k1_xboole_0),X1)|r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 15.11/15.30  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk2_0))|r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))|~r2_hidden(X2,esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 15.11/15.30  cnf(c_0_35, negated_conjecture, (k1_xboole_0=X1|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 15.11/15.30  cnf(c_0_36, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 15.11/15.30  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))|r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 15.11/15.30  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))|r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 15.11/15.30  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))|r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk2_0,esk4_0))|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 15.11/15.30  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))|r2_hidden(k4_tarski(X1,esk1_2(esk3_0,esk4_0)),k2_zfmisc_1(esk2_0,esk4_0))|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 15.11/15.30  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk2_0,k1_xboole_0),esk1_2(esk3_0,esk4_0)),k2_zfmisc_1(esk2_0,esk4_0))|r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk2_0,k1_xboole_0)),k2_zfmisc_1(esk4_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_35]), c_0_36])).
% 15.11/15.30  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 15.11/15.30  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 15.11/15.30  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk2_0,k1_xboole_0),esk1_2(esk3_0,esk4_0)),k2_zfmisc_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_41]), c_0_42])).
% 15.11/15.30  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_42]), ['proof']).
% 15.11/15.30  # SZS output end CNFRefutation
% 15.11/15.30  # Proof object total steps             : 46
% 15.11/15.30  # Proof object clause steps            : 35
% 15.11/15.30  # Proof object formula steps           : 11
% 15.11/15.30  # Proof object conjectures             : 19
% 15.11/15.30  # Proof object clause conjectures      : 16
% 15.11/15.30  # Proof object formula conjectures     : 3
% 15.11/15.30  # Proof object initial clauses used    : 12
% 15.11/15.30  # Proof object initial formulas used   : 5
% 15.11/15.30  # Proof object generating inferences   : 21
% 15.11/15.30  # Proof object simplifying inferences  : 6
% 15.11/15.30  # Training examples: 0 positive, 0 negative
% 15.11/15.30  # Parsed axioms                        : 5
% 15.11/15.30  # Removed by relevancy pruning/SinE    : 0
% 15.11/15.30  # Initial clauses                      : 15
% 15.11/15.30  # Removed in clause preprocessing      : 0
% 15.11/15.30  # Initial clauses in saturation        : 15
% 15.11/15.30  # Processed clauses                    : 27760
% 15.11/15.30  # ...of these trivial                  : 2
% 15.11/15.30  # ...subsumed                          : 21561
% 15.11/15.30  # ...remaining for further processing  : 6197
% 15.11/15.30  # Other redundant clauses eliminated   : 6
% 15.11/15.30  # Clauses deleted for lack of memory   : 0
% 15.11/15.30  # Backward-subsumed                    : 1626
% 15.11/15.30  # Backward-rewritten                   : 196
% 15.11/15.30  # Generated clauses                    : 1394614
% 15.11/15.30  # ...of the previous two non-trivial   : 1289739
% 15.11/15.30  # Contextual simplify-reflections      : 7
% 15.11/15.30  # Paramodulations                      : 1389556
% 15.11/15.30  # Factorizations                       : 5052
% 15.11/15.30  # Equation resolutions                 : 6
% 15.11/15.30  # Propositional unsat checks           : 0
% 15.11/15.30  #    Propositional check models        : 0
% 15.11/15.30  #    Propositional check unsatisfiable : 0
% 15.11/15.30  #    Propositional clauses             : 0
% 15.11/15.30  #    Propositional clauses after purity: 0
% 15.11/15.30  #    Propositional unsat core size     : 0
% 15.11/15.30  #    Propositional preprocessing time  : 0.000
% 15.11/15.30  #    Propositional encoding time       : 0.000
% 15.11/15.30  #    Propositional solver time         : 0.000
% 15.11/15.30  #    Success case prop preproc time    : 0.000
% 15.11/15.30  #    Success case prop encoding time   : 0.000
% 15.11/15.30  #    Success case prop solver time     : 0.000
% 15.11/15.30  # Current number of processed clauses  : 4357
% 15.11/15.30  #    Positive orientable unit clauses  : 8
% 15.11/15.30  #    Positive unorientable unit clauses: 0
% 15.11/15.30  #    Negative unit clauses             : 3
% 15.11/15.30  #    Non-unit-clauses                  : 4346
% 15.11/15.30  # Current number of unprocessed clauses: 1255348
% 15.11/15.30  # ...number of literals in the above   : 8642293
% 15.11/15.30  # Current number of archived formulas  : 0
% 15.11/15.30  # Current number of archived clauses   : 1836
% 15.11/15.30  # Clause-clause subsumption calls (NU) : 3502663
% 15.11/15.30  # Rec. Clause-clause subsumption calls : 380392
% 15.11/15.30  # Non-unit clause-clause subsumptions  : 23178
% 15.11/15.30  # Unit Clause-clause subsumption calls : 3132
% 15.11/15.30  # Rewrite failures with RHS unbound    : 0
% 15.11/15.30  # BW rewrite match attempts            : 12
% 15.11/15.30  # BW rewrite match successes           : 4
% 15.11/15.30  # Condensation attempts                : 0
% 15.11/15.30  # Condensation successes               : 0
% 15.11/15.30  # Termbank termtop insertions          : 42422126
% 15.11/15.35  
% 15.11/15.35  # -------------------------------------------------
% 15.11/15.35  # User time                : 14.543 s
% 15.11/15.35  # System time              : 0.460 s
% 15.11/15.35  # Total time               : 15.003 s
% 15.11/15.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
