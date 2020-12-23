%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 366 expanded)
%              Number of clauses        :   41 ( 163 expanded)
%              Number of leaves         :    5 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 (1297 expanded)
%              Number of equality atoms :   44 ( 459 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)) )
      & ( r2_hidden(X16,X18)
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)) )
      & ( ~ r2_hidden(X15,X17)
        | ~ r2_hidden(X16,X18)
        | r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_7,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9])).

fof(c_0_17,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r1_tarski(esk6_0,X2)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_8])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_25,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk3_0)
    | r1_tarski(esk5_0,X1)
    | r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_24])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk1_2(X1,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),esk4_0)
    | r1_tarski(esk6_0,X1)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk5_0,X1),esk3_0)
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r2_hidden(esk1_2(X1,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( X1 = esk6_0
    | r1_tarski(esk5_0,esk3_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk6_0,X1),esk4_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = esk4_0
    | r1_tarski(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_41]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = esk4_0
    | esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_43]),c_0_42])])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_44]),c_0_39])])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk6_0 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_50])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:27:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.19/0.37  fof(c_0_6, plain, ![X15, X16, X17, X18]:(((r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)))&(r2_hidden(X16,X18)|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18))))&(~r2_hidden(X15,X17)|~r2_hidden(X16,X18)|r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(esk3_0!=esk5_0|esk4_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.37  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_9, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))|~r2_hidden(X2,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.37  fof(c_0_12, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_9])).
% 0.19/0.37  fof(c_0_17, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_10, c_0_9])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk3_0)|r1_tarski(esk6_0,X2)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X2,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_8])).
% 0.19/0.37  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_8])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_25, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.37  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk3_0)|r1_tarski(esk5_0,X1)|r1_tarski(esk6_0,X2)), inference(spm,[status(thm)],[c_0_19, c_0_15])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_21])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_24])).
% 0.19/0.37  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (r1_tarski(esk5_0,esk3_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,esk6_0)|~r2_hidden(esk1_2(X1,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),esk4_0)|r1_tarski(esk6_0,X1)|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_15])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_2(esk5_0,X1),esk3_0)|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_15])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (r1_tarski(X1,esk5_0)|~r2_hidden(esk1_2(X1,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (X1=esk6_0|r1_tarski(esk5_0,esk3_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_15])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk1_2(esk6_0,X1),esk4_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_21])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_15])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (esk6_0=esk4_0|r1_tarski(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (esk3_0!=esk5_0|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_41]), c_0_42])])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (esk6_0=esk4_0|esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_43]), c_0_42])])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_44]), c_0_39])])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (esk6_0=k1_xboole_0|esk6_0!=esk4_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (esk6_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_22])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_50])]), c_0_24]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 52
% 0.19/0.37  # Proof object clause steps            : 41
% 0.19/0.37  # Proof object formula steps           : 11
% 0.19/0.37  # Proof object conjectures             : 37
% 0.19/0.37  # Proof object clause conjectures      : 34
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 11
% 0.19/0.37  # Proof object initial formulas used   : 5
% 0.19/0.37  # Proof object generating inferences   : 29
% 0.19/0.37  # Proof object simplifying inferences  : 13
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 5
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 14
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 14
% 0.19/0.37  # Processed clauses                    : 74
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 11
% 0.19/0.37  # ...remaining for further processing  : 63
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 9
% 0.19/0.37  # Backward-rewritten                   : 33
% 0.19/0.37  # Generated clauses                    : 146
% 0.19/0.37  # ...of the previous two non-trivial   : 122
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 144
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 19
% 0.19/0.37  #    Positive orientable unit clauses  : 3
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 14
% 0.19/0.37  # Current number of unprocessed clauses: 46
% 0.19/0.37  # ...number of literals in the above   : 154
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 42
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 226
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 175
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 20
% 0.19/0.37  # Unit Clause-clause subsumption calls : 18
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2287
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
