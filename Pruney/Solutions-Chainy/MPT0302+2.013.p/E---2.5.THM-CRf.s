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
% DateTime   : Thu Dec  3 10:43:32 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 171 expanded)
%              Number of clauses        :   33 (  77 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 575 expanded)
%              Number of equality atoms :   33 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

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

fof(c_0_7,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X13)
        | r2_hidden(X11,X12)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_8,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_17,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(esk2_2(X14,X15),X14)
        | ~ r2_hidden(esk2_2(X14,X15),X15)
        | X14 = X15 )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r2_hidden(esk2_2(X14,X15),X15)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X21,X23)
        | r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_25,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(X2,esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | r2_hidden(k4_tarski(esk2_2(k1_xboole_0,X1),esk2_2(k1_xboole_0,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_xboole_0,esk3_0),esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_35,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(esk1_2(X2,X3),esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X2,X1))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))
    | r1_tarski(X2,X3)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_xboole_0,esk4_0),esk1_2(X1,X2)),k2_zfmisc_1(esk4_0,X1))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.68  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.46/0.68  # and selection function SelectNewComplexAHPNS.
% 0.46/0.68  #
% 0.46/0.68  # Preprocessing time       : 0.028 s
% 0.46/0.68  
% 0.46/0.68  # Proof found!
% 0.46/0.68  # SZS status Theorem
% 0.46/0.68  # SZS output start CNFRefutation
% 0.46/0.68  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.46/0.68  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.46/0.68  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.46/0.68  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.46/0.68  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.46/0.68  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 0.46/0.68  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.46/0.68  fof(c_0_7, plain, ![X11, X12, X13]:(((~r2_hidden(X11,X12)|~r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13)))&(r2_hidden(X11,X12)|r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13))))&((~r2_hidden(X11,X12)|r2_hidden(X11,X13)|r2_hidden(X11,k5_xboole_0(X12,X13)))&(~r2_hidden(X11,X13)|r2_hidden(X11,X12)|r2_hidden(X11,k5_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.46/0.68  fof(c_0_8, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.46/0.68  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.68  cnf(c_0_10, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.68  fof(c_0_11, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.46/0.68  cnf(c_0_12, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.46/0.68  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.46/0.68  cnf(c_0_14, plain, (r1_tarski(k1_xboole_0,X1)|~r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.46/0.68  cnf(c_0_15, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.46/0.68  cnf(c_0_16, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.46/0.68  fof(c_0_17, plain, ![X14, X15]:((~r2_hidden(esk2_2(X14,X15),X14)|~r2_hidden(esk2_2(X14,X15),X15)|X14=X15)&(r2_hidden(esk2_2(X14,X15),X14)|r2_hidden(esk2_2(X14,X15),X15)|X14=X15)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.46/0.68  fof(c_0_18, plain, ![X20, X21, X22, X23]:(((r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))&(r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23))))&(~r2_hidden(X20,X22)|~r2_hidden(X21,X23)|r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.46/0.68  cnf(c_0_19, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])).
% 0.46/0.68  cnf(c_0_20, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.68  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 0.46/0.68  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.68  cnf(c_0_23, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.46/0.68  fof(c_0_24, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk3_0!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.46/0.68  cnf(c_0_25, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(X2,esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X3,X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.46/0.68  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.68  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.68  cnf(c_0_28, plain, (k1_xboole_0=X1|k1_xboole_0=X2|r2_hidden(k4_tarski(esk2_2(k1_xboole_0,X1),esk2_2(k1_xboole_0,X2)),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.46/0.68  cnf(c_0_29, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.68  cnf(c_0_30, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.68  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.68  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.46/0.68  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(k1_xboole_0,esk3_0),esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk4_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_29]), c_0_30])).
% 0.46/0.68  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.46/0.68  cnf(c_0_35, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(esk1_2(X2,X3),esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X2,X1))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_25, c_0_13])).
% 0.46/0.68  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))|r1_tarski(X2,X3)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_22, c_0_13])).
% 0.46/0.68  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.46/0.68  fof(c_0_38, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.46/0.68  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.46/0.68  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])).
% 0.46/0.68  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(k1_xboole_0,esk4_0),esk1_2(X1,X2)),k2_zfmisc_1(esk4_0,X1))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.46/0.68  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.46/0.68  cnf(c_0_43, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.46/0.68  cnf(c_0_44, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.68  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 0.46/0.68  cnf(c_0_46, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.46/0.68  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_45]), c_0_46]), ['proof']).
% 0.46/0.68  # SZS output end CNFRefutation
% 0.46/0.68  # Proof object total steps             : 48
% 0.46/0.68  # Proof object clause steps            : 33
% 0.46/0.68  # Proof object formula steps           : 15
% 0.46/0.68  # Proof object conjectures             : 17
% 0.46/0.68  # Proof object clause conjectures      : 14
% 0.46/0.68  # Proof object formula conjectures     : 3
% 0.46/0.68  # Proof object initial clauses used    : 14
% 0.46/0.68  # Proof object initial formulas used   : 7
% 0.46/0.68  # Proof object generating inferences   : 19
% 0.46/0.68  # Proof object simplifying inferences  : 6
% 0.46/0.68  # Training examples: 0 positive, 0 negative
% 0.46/0.68  # Parsed axioms                        : 7
% 0.46/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.68  # Initial clauses                      : 20
% 0.46/0.68  # Removed in clause preprocessing      : 0
% 0.46/0.68  # Initial clauses in saturation        : 20
% 0.46/0.68  # Processed clauses                    : 1244
% 0.46/0.68  # ...of these trivial                  : 10
% 0.46/0.68  # ...subsumed                          : 190
% 0.46/0.68  # ...remaining for further processing  : 1044
% 0.46/0.68  # Other redundant clauses eliminated   : 2
% 0.46/0.68  # Clauses deleted for lack of memory   : 0
% 0.46/0.68  # Backward-subsumed                    : 0
% 0.46/0.68  # Backward-rewritten                   : 76
% 0.46/0.68  # Generated clauses                    : 30514
% 0.46/0.68  # ...of the previous two non-trivial   : 28494
% 0.46/0.68  # Contextual simplify-reflections      : 2
% 0.46/0.68  # Paramodulations                      : 30452
% 0.46/0.68  # Factorizations                       : 60
% 0.46/0.68  # Equation resolutions                 : 2
% 0.46/0.68  # Propositional unsat checks           : 0
% 0.46/0.68  #    Propositional check models        : 0
% 0.46/0.68  #    Propositional check unsatisfiable : 0
% 0.46/0.68  #    Propositional clauses             : 0
% 0.46/0.68  #    Propositional clauses after purity: 0
% 0.46/0.68  #    Propositional unsat core size     : 0
% 0.46/0.68  #    Propositional preprocessing time  : 0.000
% 0.46/0.68  #    Propositional encoding time       : 0.000
% 0.46/0.68  #    Propositional solver time         : 0.000
% 0.46/0.68  #    Success case prop preproc time    : 0.000
% 0.46/0.68  #    Success case prop encoding time   : 0.000
% 0.46/0.68  #    Success case prop solver time     : 0.000
% 0.46/0.68  # Current number of processed clauses  : 966
% 0.46/0.68  #    Positive orientable unit clauses  : 781
% 0.46/0.68  #    Positive unorientable unit clauses: 0
% 0.46/0.68  #    Negative unit clauses             : 7
% 0.46/0.68  #    Non-unit-clauses                  : 178
% 0.46/0.68  # Current number of unprocessed clauses: 27143
% 0.46/0.68  # ...number of literals in the above   : 60618
% 0.46/0.68  # Current number of archived formulas  : 0
% 0.46/0.68  # Current number of archived clauses   : 76
% 0.46/0.68  # Clause-clause subsumption calls (NU) : 5882
% 0.46/0.68  # Rec. Clause-clause subsumption calls : 3959
% 0.46/0.68  # Non-unit clause-clause subsumptions  : 173
% 0.46/0.68  # Unit Clause-clause subsumption calls : 319
% 0.46/0.68  # Rewrite failures with RHS unbound    : 0
% 0.46/0.68  # BW rewrite match attempts            : 82630
% 0.46/0.68  # BW rewrite match successes           : 11
% 0.46/0.68  # Condensation attempts                : 0
% 0.46/0.68  # Condensation successes               : 0
% 0.46/0.68  # Termbank termtop insertions          : 743272
% 0.46/0.68  
% 0.46/0.68  # -------------------------------------------------
% 0.46/0.68  # User time                : 0.309 s
% 0.46/0.68  # System time              : 0.013 s
% 0.46/0.68  # Total time               : 0.323 s
% 0.46/0.68  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
