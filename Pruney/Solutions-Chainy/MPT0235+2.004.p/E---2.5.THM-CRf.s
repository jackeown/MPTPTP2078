%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:18 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 144 expanded)
%              Number of clauses        :   29 (  61 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 341 expanded)
%              Number of equality atoms :   84 ( 241 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_zfmisc_1,conjecture,(
    ! [X1] : k1_zfmisc_1(k1_tarski(X1)) = k2_tarski(k1_xboole_0,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] : k1_zfmisc_1(k1_tarski(X1)) = k2_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(assume_negation,[status(cth)],[t30_zfmisc_1])).

fof(c_0_7,negated_conjecture,(
    k1_zfmisc_1(k1_tarski(esk3_0)) != k2_tarski(k1_xboole_0,k1_tarski(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk2_2(X21,X22),X22)
        | ~ r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk2_2(X21,X22),X22)
        | r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_12,negated_conjecture,
    ( k1_zfmisc_1(k1_tarski(esk3_0)) != k2_tarski(k1_xboole_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | esk1_3(X1,X2,X3) = X1
    | esk1_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r1_tarski(X24,k2_tarski(X25,X26))
        | X24 = k1_xboole_0
        | X24 = k1_tarski(X25)
        | X24 = k1_tarski(X26)
        | X24 = k2_tarski(X25,X26) )
      & ( X24 != k1_xboole_0
        | r1_tarski(X24,k2_tarski(X25,X26)) )
      & ( X24 != k1_tarski(X25)
        | r1_tarski(X24,k2_tarski(X25,X26)) )
      & ( X24 != k1_tarski(X26)
        | r1_tarski(X24,k2_tarski(X25,X26)) )
      & ( X24 != k2_tarski(X25,X26)
        | r1_tarski(X24,k2_tarski(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)) != k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_19,plain,
    ( X3 = k1_enumset1(X1,X1,X2)
    | esk1_3(X1,X2,X3) = X2
    | esk1_3(X1,X2,X3) = X1
    | r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_20,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_enumset1(esk3_0,esk3_0,esk3_0)
    | esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X1
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( X3 = k1_enumset1(X1,X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X3,X3,X3)
    | X1 = k1_enumset1(X2,X2,X3)
    | X1 = k1_enumset1(X2,X2,X2)
    | ~ r1_tarski(X1,k1_enumset1(X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_13]),c_0_13]),c_0_14]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_enumset1(esk3_0,esk3_0,esk3_0)
    | esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0
    | r1_tarski(esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k1_enumset1(X2,X2,X3))
    | X1 != k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( X3 = k1_enumset1(X1,X1,X2)
    | esk1_3(X1,X2,X3) != X1
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_34,plain,
    ( k1_zfmisc_1(X1) = k1_enumset1(X2,X2,X3)
    | esk1_3(X2,X3,k1_zfmisc_1(X1)) != X3
    | ~ r1_tarski(esk1_3(X2,X3,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_enumset1(esk3_0,esk3_0,esk3_0)
    | esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k1_enumset1(X2,X2,X3))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_14])).

cnf(c_0_38,plain,
    ( k1_zfmisc_1(X1) = k1_enumset1(X2,X2,X3)
    | esk1_3(X2,X3,k1_zfmisc_1(X1)) != X2
    | ~ r1_tarski(esk1_3(X2,X3,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),c_0_18])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t30_zfmisc_1, conjecture, ![X1]:k1_zfmisc_1(k1_tarski(X1))=k2_tarski(k1_xboole_0,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_zfmisc_1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.38  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:k1_zfmisc_1(k1_tarski(X1))=k2_tarski(k1_xboole_0,k1_tarski(X1))), inference(assume_negation,[status(cth)],[t30_zfmisc_1])).
% 0.14/0.38  fof(c_0_7, negated_conjecture, k1_zfmisc_1(k1_tarski(esk3_0))!=k2_tarski(k1_xboole_0,k1_tarski(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_9, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_10, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk2_2(X21,X22),X22)|~r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk2_2(X21,X22),X22)|r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (k1_zfmisc_1(k1_tarski(esk3_0))!=k2_tarski(k1_xboole_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|esk1_3(X1,X2,X3)=X1|esk1_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_16, plain, ![X24, X25, X26]:((~r1_tarski(X24,k2_tarski(X25,X26))|(X24=k1_xboole_0|X24=k1_tarski(X25)|X24=k1_tarski(X26)|X24=k2_tarski(X25,X26)))&((((X24!=k1_xboole_0|r1_tarski(X24,k2_tarski(X25,X26)))&(X24!=k1_tarski(X25)|r1_tarski(X24,k2_tarski(X25,X26))))&(X24!=k1_tarski(X26)|r1_tarski(X24,k2_tarski(X25,X26))))&(X24!=k2_tarski(X25,X26)|r1_tarski(X24,k2_tarski(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.14/0.38  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))!=k1_enumset1(k1_xboole_0,k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13]), c_0_14]), c_0_14]), c_0_14])).
% 0.14/0.38  cnf(c_0_19, plain, (X3=k1_enumset1(X1,X1,X2)|esk1_3(X1,X2,X3)=X2|esk1_3(X1,X2,X3)=X1|r2_hidden(esk1_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.14/0.38  cnf(c_0_20, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_22, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_enumset1(esk3_0,esk3_0,esk3_0)|esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19])])).
% 0.14/0.38  cnf(c_0_25, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_26, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X1|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_27, plain, (X3=k1_enumset1(X1,X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.14/0.38  cnf(c_0_28, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_29, plain, (X1=k1_xboole_0|X1=k1_enumset1(X3,X3,X3)|X1=k1_enumset1(X2,X2,X3)|X1=k1_enumset1(X2,X2,X2)|~r1_tarski(X1,k1_enumset1(X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_13]), c_0_13]), c_0_14]), c_0_14]), c_0_14]), c_0_14])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_enumset1(esk3_0,esk3_0,esk3_0)|esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0|r1_tarski(esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))),k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_31, plain, (r1_tarski(X1,k1_enumset1(X2,X2,X3))|X1!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_13]), c_0_14]), c_0_14])).
% 0.14/0.38  cnf(c_0_32, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_33, plain, (X3=k1_enumset1(X1,X1,X2)|esk1_3(X1,X2,X3)!=X1|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[c_0_26, c_0_14])).
% 0.14/0.38  cnf(c_0_34, plain, (k1_zfmisc_1(X1)=k1_enumset1(X2,X2,X3)|esk1_3(X2,X3,k1_zfmisc_1(X1))!=X3|~r1_tarski(esk1_3(X2,X3,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_enumset1(esk3_0,esk3_0,esk3_0)|esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_36, plain, (r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_37, plain, (r1_tarski(X1,k1_enumset1(X2,X2,X3))|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_14])).
% 0.14/0.38  cnf(c_0_38, plain, (k1_zfmisc_1(X1)=k1_enumset1(X2,X2,X3)|esk1_3(X2,X3,k1_zfmisc_1(X1))!=X2|~r1_tarski(esk1_3(X2,X3,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (esk1_3(k1_xboole_0,k1_enumset1(esk3_0,esk3_0,esk3_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), c_0_18])).
% 0.14/0.38  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[c_0_37])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])]), c_0_18]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 42
% 0.14/0.38  # Proof object clause steps            : 29
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 10
% 0.14/0.38  # Proof object clause conjectures      : 7
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 7
% 0.14/0.38  # Proof object simplifying inferences  : 29
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 18
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 16
% 0.14/0.38  # Processed clauses                    : 50
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 50
% 0.14/0.38  # Other redundant clauses eliminated   : 17
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 116
% 0.14/0.38  # ...of the previous two non-trivial   : 95
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 100
% 0.14/0.38  # Factorizations                       : 1
% 0.14/0.38  # Equation resolutions                 : 17
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
% 0.14/0.38  # Current number of processed clauses  : 22
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 14
% 0.14/0.38  # Current number of unprocessed clauses: 76
% 0.14/0.38  # ...number of literals in the above   : 376
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 21
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 15
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 14
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 9
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3207
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
