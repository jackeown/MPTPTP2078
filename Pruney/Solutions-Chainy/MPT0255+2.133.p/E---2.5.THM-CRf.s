%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:36 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 (  35 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 151 expanded)
%              Number of equality atoms :  105 ( 116 expanded)
%              Maximal formula depth    :   57 (   6 average)
%              Maximal clause size      :   84 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(t15_xboole_1,axiom,(
    ! [X1,X2] :
      ( k2_xboole_0(X1,X2) = k1_xboole_0
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(d8_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11] :
      ( X11 = k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
    <=> ! [X12] :
          ( r2_hidden(X12,X11)
        <=> ~ ( X12 != X1
              & X12 != X2
              & X12 != X3
              & X12 != X4
              & X12 != X5
              & X12 != X6
              & X12 != X7
              & X12 != X8
              & X12 != X9
              & X12 != X10 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X13,X14] :
      ( k2_xboole_0(X13,X14) != k1_xboole_0
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).

fof(c_0_9,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X45,X46] : k3_xboole_0(k1_tarski(X45),k2_tarski(X45,X46)) = k1_tarski(X45) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X15] : k3_xboole_0(X15,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_14,plain,(
    ! [X42,X43,X44] :
      ( ( ~ r2_hidden(X42,X44)
        | k4_xboole_0(k2_tarski(X42,X43),X44) != k1_tarski(X42) )
      & ( r2_hidden(X43,X44)
        | X42 = X43
        | k4_xboole_0(k2_tarski(X42,X43),X44) != k1_tarski(X42) )
      & ( ~ r2_hidden(X43,X44)
        | r2_hidden(X42,X44)
        | k4_xboole_0(k2_tarski(X42,X43),X44) = k1_tarski(X42) )
      & ( X42 != X43
        | r2_hidden(X42,X44)
        | k4_xboole_0(k2_tarski(X42,X43),X44) = k1_tarski(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

fof(c_0_15,plain,(
    ! [X16] : k4_xboole_0(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_16,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X17
        | X28 = X18
        | X28 = X19
        | X28 = X20
        | X28 = X21
        | X28 = X22
        | X28 = X23
        | X28 = X24
        | X28 = X25
        | X28 = X26
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X17
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X18
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X19
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X20
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X21
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X22
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X23
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X24
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X25
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X30
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X31
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X32
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X33
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X34
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X35
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X36
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X37
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X38
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) != X39
        | ~ r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X30
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X31
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X32
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X33
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X34
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X35
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X36
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X37
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X38
        | esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40) = X39
        | X40 = k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_enumset1])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k1_tarski(esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k8_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X12,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_21]),c_0_22])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k8_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X10,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:46:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.12/0.37  fof(t15_xboole_1, axiom, ![X1, X2]:(k2_xboole_0(X1,X2)=k1_xboole_0=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 0.12/0.37  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 0.12/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.37  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 0.12/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.12/0.37  fof(d8_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11]:(X11=k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)<=>![X12]:(r2_hidden(X12,X11)<=>~((((((((((X12!=X1&X12!=X2)&X12!=X3)&X12!=X4)&X12!=X5)&X12!=X6)&X12!=X7)&X12!=X8)&X12!=X9)&X12!=X10)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_enumset1)).
% 0.12/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.12/0.37  fof(c_0_8, plain, ![X13, X14]:(k2_xboole_0(X13,X14)!=k1_xboole_0|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.37  fof(c_0_10, plain, ![X45, X46]:k3_xboole_0(k1_tarski(X45),k2_tarski(X45,X46))=k1_tarski(X45), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 0.12/0.37  cnf(c_0_11, plain, (X1=k1_xboole_0|k2_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  fof(c_0_13, plain, ![X15]:k3_xboole_0(X15,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.37  fof(c_0_14, plain, ![X42, X43, X44]:(((~r2_hidden(X42,X44)|k4_xboole_0(k2_tarski(X42,X43),X44)!=k1_tarski(X42))&(r2_hidden(X43,X44)|X42=X43|k4_xboole_0(k2_tarski(X42,X43),X44)!=k1_tarski(X42)))&((~r2_hidden(X43,X44)|r2_hidden(X42,X44)|k4_xboole_0(k2_tarski(X42,X43),X44)=k1_tarski(X42))&(X42!=X43|r2_hidden(X42,X44)|k4_xboole_0(k2_tarski(X42,X43),X44)=k1_tarski(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 0.12/0.37  fof(c_0_15, plain, ![X16]:k4_xboole_0(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.12/0.37  cnf(c_0_16, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (k2_tarski(esk2_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.37  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_19, plain, ![X17, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X28,X27)|(X28=X17|X28=X18|X28=X19|X28=X20|X28=X21|X28=X22|X28=X23|X28=X24|X28=X25|X28=X26)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26))&((((((((((X29!=X17|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26))&(X29!=X18|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X19|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X20|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X21|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X22|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X23|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X24|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X25|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26)))&(X29!=X26|r2_hidden(X29,X27)|X27!=k8_enumset1(X17,X18,X19,X20,X21,X22,X23,X24,X25,X26))))&(((((((((((esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X30|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X31|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X32|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X33|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X34|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X35|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X36|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X37|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X38|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)!=X39|~r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(r2_hidden(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40),X40)|(esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X30|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X31|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X32|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X33|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X34|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X35|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X36|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X37|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X38|esk1_11(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40)=X39)|X40=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_enumset1])])])])])])).
% 0.12/0.37  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)!=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (k1_tarski(esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.12/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k8_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X12,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (~r2_hidden(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_21]), c_0_22])])).
% 0.12/0.37  cnf(c_0_25, plain, (r2_hidden(X1,k8_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X10,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 27
% 0.12/0.37  # Proof object clause steps            : 12
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 8
% 0.12/0.37  # Proof object clause conjectures      : 5
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 7
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 4
% 0.12/0.37  # Proof object simplifying inferences  : 6
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 31
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 31
% 0.12/0.37  # Processed clauses                    : 59
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 59
% 0.12/0.37  # Other redundant clauses eliminated   : 22
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 23
% 0.12/0.37  # ...of the previous two non-trivial   : 18
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 11
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 22
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 15
% 0.12/0.37  #    Positive orientable unit clauses  : 8
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 6
% 0.12/0.37  # Current number of unprocessed clauses: 21
% 0.12/0.37  # ...number of literals in the above   : 62
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 32
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 105
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 103
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 46
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1902
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.025 s
% 0.12/0.37  # System time              : 0.007 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
