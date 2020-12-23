%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:19 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 102 expanded)
%              Number of clauses        :   26 (  46 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 145 expanded)
%              Number of equality atoms :   45 ( 102 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X19,X20] : k2_tarski(X19,X20) = k2_xboole_0(k1_tarski(X19),k1_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_13,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X22),X23),X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk2_0),k2_tarski(esk3_0,esk3_0)) = k2_tarski(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_21]),c_0_21]),c_0_21])).

fof(c_0_29,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X12
        | X13 != k1_tarski(X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_tarski(X12) )
      & ( ~ r2_hidden(esk1_2(X16,X17),X17)
        | esk1_2(X16,X17) != X16
        | X17 = k1_tarski(X16) )
      & ( r2_hidden(esk1_2(X16,X17),X17)
        | esk1_2(X16,X17) = X16
        | X17 = k1_tarski(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k2_tarski(X1,X1),X2),X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = k2_tarski(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_35,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_xboole_0(k2_tarski(X1,X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk3_0),k2_tarski(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( k2_tarski(esk3_0,esk2_0) = k2_tarski(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_37]),c_0_27])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,k2_tarski(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:18:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S083N
% 0.12/0.40  # and selection function SelectCQArNT.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.049 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.12/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.40  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.40  fof(l20_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 0.12/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.40  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.12/0.40  fof(c_0_10, plain, ![X10, X11]:r1_tarski(X10,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.40  fof(c_0_11, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.40  fof(c_0_12, plain, ![X19, X20]:k2_tarski(X19,X20)=k2_xboole_0(k1_tarski(X19),k1_tarski(X20)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.40  fof(c_0_13, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.40  fof(c_0_14, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.40  fof(c_0_15, plain, ![X22, X23]:(~r1_tarski(k2_xboole_0(k1_tarski(X22),X23),X23)|r2_hidden(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).
% 0.12/0.40  fof(c_0_16, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.40  fof(c_0_17, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.40  cnf(c_0_18, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.40  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.40  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.40  cnf(c_0_22, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.40  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.12/0.40  cnf(c_0_28, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk2_0),k2_tarski(esk3_0,esk3_0))=k2_tarski(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.40  fof(c_0_29, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|X14=X12|X13!=k1_tarski(X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_tarski(X12)))&((~r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)!=X16|X17=k1_tarski(X16))&(r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)=X16|X17=k1_tarski(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.40  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k2_tarski(X1,X1),X2),X2)), inference(rw,[status(thm)],[c_0_23, c_0_21])).
% 0.12/0.40  cnf(c_0_31, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.12/0.40  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.12/0.40  cnf(c_0_33, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.40  cnf(c_0_34, negated_conjecture, (k2_tarski(esk2_0,esk3_0)=k2_tarski(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.12/0.40  cnf(c_0_35, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.40  cnf(c_0_36, plain, (r2_hidden(X1,k2_xboole_0(k2_tarski(X1,X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.12/0.40  cnf(c_0_37, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk3_0),k2_tarski(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.40  cnf(c_0_38, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_21])).
% 0.12/0.40  cnf(c_0_39, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.12/0.40  cnf(c_0_40, negated_conjecture, (k2_tarski(esk3_0,esk2_0)=k2_tarski(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_37]), c_0_27])).
% 0.12/0.40  cnf(c_0_41, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_38])).
% 0.12/0.40  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,k2_tarski(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.40  cnf(c_0_43, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 45
% 0.12/0.40  # Proof object clause steps            : 26
% 0.12/0.40  # Proof object formula steps           : 19
% 0.12/0.40  # Proof object conjectures             : 11
% 0.12/0.40  # Proof object clause conjectures      : 8
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 10
% 0.12/0.40  # Proof object initial formulas used   : 9
% 0.12/0.40  # Proof object generating inferences   : 9
% 0.12/0.40  # Proof object simplifying inferences  : 14
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 9
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 15
% 0.12/0.40  # Removed in clause preprocessing      : 1
% 0.12/0.40  # Initial clauses in saturation        : 14
% 0.12/0.40  # Processed clauses                    : 59
% 0.12/0.40  # ...of these trivial                  : 3
% 0.12/0.40  # ...subsumed                          : 9
% 0.12/0.40  # ...remaining for further processing  : 47
% 0.12/0.40  # Other redundant clauses eliminated   : 5
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 0
% 0.12/0.40  # Backward-rewritten                   : 2
% 0.12/0.40  # Generated clauses                    : 84
% 0.12/0.40  # ...of the previous two non-trivial   : 51
% 0.12/0.40  # Contextual simplify-reflections      : 0
% 0.12/0.40  # Paramodulations                      : 80
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 5
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 28
% 0.12/0.40  #    Positive orientable unit clauses  : 14
% 0.12/0.40  #    Positive unorientable unit clauses: 2
% 0.12/0.40  #    Negative unit clauses             : 1
% 0.12/0.40  #    Non-unit-clauses                  : 11
% 0.12/0.40  # Current number of unprocessed clauses: 19
% 0.12/0.40  # ...number of literals in the above   : 28
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 16
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 26
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 26
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 9
% 0.12/0.40  # Unit Clause-clause subsumption calls : 2
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 23
% 0.12/0.40  # BW rewrite match successes           : 14
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 1348
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.049 s
% 0.12/0.40  # System time              : 0.007 s
% 0.12/0.40  # Total time               : 0.056 s
% 0.12/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
