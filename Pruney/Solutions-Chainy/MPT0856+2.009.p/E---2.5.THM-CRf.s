%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:02 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 107 expanded)
%              Number of clauses        :   29 (  46 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 192 expanded)
%              Number of equality atoms :   41 (  95 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
       => ( k1_mcart_1(X1) = X2
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t12_mcart_1])).

fof(c_0_11,plain,(
    ! [X25] : k1_ordinal1(X25) = k2_xboole_0(X25,k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_12,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | ~ r2_hidden(k2_mcart_1(esk2_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X23)
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( X22 != X24
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( ~ r2_hidden(X22,X23)
        | X22 = X24
        | r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X26] : r2_hidden(X26,k1_ordinal1(X26)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_18,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(k1_mcart_1(X27),X28)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) )
      & ( r2_hidden(k2_mcart_1(X27),X29)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | k2_xboole_0(k1_tarski(X20),X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_26,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_19]),c_0_23]),c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_19]),c_0_23]),c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_23]),c_0_24])).

cnf(c_0_35,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_19]),c_0_23]),c_0_24])).

cnf(c_0_39,plain,
    ( X1 = X2
    | r2_hidden(X1,k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_23]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2))) = k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2))
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | ~ r2_hidden(k2_mcart_1(esk2_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = X1
    | r2_hidden(k1_mcart_1(esk2_0),k4_xboole_0(k2_xboole_0(esk3_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.49/0.68  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.49/0.68  # and selection function SelectCQIArNpEqFirst.
% 0.49/0.68  #
% 0.49/0.68  # Preprocessing time       : 0.027 s
% 0.49/0.68  # Presaturation interreduction done
% 0.49/0.68  
% 0.49/0.68  # Proof found!
% 0.49/0.68  # SZS status Theorem
% 0.49/0.68  # SZS output start CNFRefutation
% 0.49/0.68  fof(t12_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.49/0.68  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.49/0.68  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.49/0.68  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.49/0.68  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.49/0.68  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.49/0.68  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.49/0.68  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.49/0.68  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.49/0.68  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.49/0.68  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3)))), inference(assume_negation,[status(cth)],[t12_mcart_1])).
% 0.49/0.68  fof(c_0_11, plain, ![X25]:k1_ordinal1(X25)=k2_xboole_0(X25,k1_tarski(X25)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.49/0.68  fof(c_0_12, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.49/0.68  fof(c_0_13, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))&(k1_mcart_1(esk2_0)!=esk3_0|~r2_hidden(k2_mcart_1(esk2_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.49/0.68  fof(c_0_14, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.49/0.68  fof(c_0_15, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.49/0.68  fof(c_0_16, plain, ![X22, X23, X24]:(((r2_hidden(X22,X23)|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))&(X22!=X24|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24)))))&(~r2_hidden(X22,X23)|X22=X24|r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.49/0.68  fof(c_0_17, plain, ![X26]:r2_hidden(X26,k1_ordinal1(X26)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.49/0.68  cnf(c_0_18, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.49/0.68  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.49/0.68  fof(c_0_20, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.49/0.68  fof(c_0_21, plain, ![X27, X28, X29]:((r2_hidden(k1_mcart_1(X27),X28)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))&(r2_hidden(k2_mcart_1(X27),X29)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.49/0.68  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.49/0.68  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.49/0.68  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.49/0.68  fof(c_0_25, plain, ![X20, X21]:(~r2_hidden(X20,X21)|k2_xboole_0(k1_tarski(X20),X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.49/0.68  cnf(c_0_26, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.68  cnf(c_0_27, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.68  cnf(c_0_28, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.49/0.68  cnf(c_0_29, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.68  cnf(c_0_30, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.49/0.68  cnf(c_0_31, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_19]), c_0_23]), c_0_24])).
% 0.49/0.68  cnf(c_0_32, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.49/0.68  cnf(c_0_33, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_19]), c_0_23]), c_0_24])).
% 0.49/0.68  cnf(c_0_34, plain, (r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_23]), c_0_24])).
% 0.49/0.68  cnf(c_0_35, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.68  cnf(c_0_36, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_29])).
% 0.49/0.68  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.49/0.68  cnf(c_0_38, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_19]), c_0_23]), c_0_24])).
% 0.49/0.68  cnf(c_0_39, plain, (X1=X2|r2_hidden(X1,k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.49/0.68  cnf(c_0_40, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.49/0.68  cnf(c_0_41, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_23]), c_0_24])).
% 0.49/0.68  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.49/0.68  cnf(c_0_43, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2)))=k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2))|X1=X2), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.49/0.68  cnf(c_0_44, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|~r2_hidden(k2_mcart_1(esk2_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.49/0.68  cnf(c_0_45, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.49/0.68  cnf(c_0_46, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_41])).
% 0.49/0.68  cnf(c_0_47, negated_conjecture, (esk3_0=X1|r2_hidden(k1_mcart_1(esk2_0),k4_xboole_0(k2_xboole_0(esk3_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.49/0.68  cnf(c_0_48, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.49/0.68  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.49/0.68  # SZS output end CNFRefutation
% 0.49/0.68  # Proof object total steps             : 50
% 0.49/0.68  # Proof object clause steps            : 29
% 0.49/0.68  # Proof object formula steps           : 21
% 0.49/0.68  # Proof object conjectures             : 12
% 0.49/0.68  # Proof object clause conjectures      : 9
% 0.49/0.68  # Proof object formula conjectures     : 3
% 0.49/0.68  # Proof object initial clauses used    : 13
% 0.49/0.68  # Proof object initial formulas used   : 10
% 0.49/0.68  # Proof object generating inferences   : 7
% 0.49/0.68  # Proof object simplifying inferences  : 21
% 0.49/0.68  # Training examples: 0 positive, 0 negative
% 0.49/0.68  # Parsed axioms                        : 10
% 0.49/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.49/0.68  # Initial clauses                      : 19
% 0.49/0.68  # Removed in clause preprocessing      : 4
% 0.49/0.68  # Initial clauses in saturation        : 15
% 0.49/0.68  # Processed clauses                    : 1916
% 0.49/0.68  # ...of these trivial                  : 372
% 0.49/0.68  # ...subsumed                          : 1114
% 0.49/0.68  # ...remaining for further processing  : 430
% 0.49/0.68  # Other redundant clauses eliminated   : 4
% 0.49/0.68  # Clauses deleted for lack of memory   : 0
% 0.49/0.68  # Backward-subsumed                    : 2
% 0.49/0.68  # Backward-rewritten                   : 3
% 0.49/0.68  # Generated clauses                    : 38955
% 0.49/0.68  # ...of the previous two non-trivial   : 21606
% 0.49/0.68  # Contextual simplify-reflections      : 7
% 0.49/0.68  # Paramodulations                      : 38819
% 0.49/0.68  # Factorizations                       : 132
% 0.49/0.68  # Equation resolutions                 : 4
% 0.49/0.68  # Propositional unsat checks           : 0
% 0.49/0.68  #    Propositional check models        : 0
% 0.49/0.68  #    Propositional check unsatisfiable : 0
% 0.49/0.68  #    Propositional clauses             : 0
% 0.49/0.68  #    Propositional clauses after purity: 0
% 0.49/0.68  #    Propositional unsat core size     : 0
% 0.49/0.68  #    Propositional preprocessing time  : 0.000
% 0.49/0.68  #    Propositional encoding time       : 0.000
% 0.49/0.68  #    Propositional solver time         : 0.000
% 0.49/0.68  #    Success case prop preproc time    : 0.000
% 0.49/0.68  #    Success case prop encoding time   : 0.000
% 0.49/0.68  #    Success case prop solver time     : 0.000
% 0.49/0.68  # Current number of processed clauses  : 406
% 0.49/0.68  #    Positive orientable unit clauses  : 214
% 0.49/0.68  #    Positive unorientable unit clauses: 0
% 0.49/0.68  #    Negative unit clauses             : 2
% 0.49/0.68  #    Non-unit-clauses                  : 190
% 0.49/0.68  # Current number of unprocessed clauses: 19712
% 0.49/0.68  # ...number of literals in the above   : 38099
% 0.49/0.68  # Current number of archived formulas  : 0
% 0.49/0.68  # Current number of archived clauses   : 24
% 0.49/0.68  # Clause-clause subsumption calls (NU) : 13383
% 0.49/0.68  # Rec. Clause-clause subsumption calls : 11411
% 0.49/0.68  # Non-unit clause-clause subsumptions  : 1123
% 0.49/0.68  # Unit Clause-clause subsumption calls : 170
% 0.49/0.68  # Rewrite failures with RHS unbound    : 0
% 0.49/0.68  # BW rewrite match attempts            : 2533
% 0.49/0.68  # BW rewrite match successes           : 3
% 0.49/0.68  # Condensation attempts                : 0
% 0.49/0.68  # Condensation successes               : 0
% 0.49/0.68  # Termbank termtop insertions          : 599080
% 0.49/0.68  
% 0.49/0.68  # -------------------------------------------------
% 0.49/0.68  # User time                : 0.317 s
% 0.49/0.68  # System time              : 0.021 s
% 0.49/0.68  # Total time               : 0.338 s
% 0.49/0.68  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
