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
% DateTime   : Thu Dec  3 10:42:20 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 292 expanded)
%              Number of clauses        :   29 ( 123 expanded)
%              Number of leaves         :    7 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  141 ( 740 expanded)
%              Number of equality atoms :   75 ( 418 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

fof(c_0_8,negated_conjecture,
    ( ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) != esk3_0
      | r2_hidden(esk4_0,esk3_0) )
    & ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) = esk3_0
      | ~ r2_hidden(esk4_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k4_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | k4_xboole_0(esk3_0,k1_tarski(esk4_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X31
        | X35 = X32
        | X35 = X33
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X31
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X32
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( esk2_4(X37,X38,X39,X40) != X37
        | ~ r2_hidden(esk2_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( esk2_4(X37,X38,X39,X40) != X38
        | ~ r2_hidden(esk2_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( esk2_4(X37,X38,X39,X40) != X39
        | ~ r2_hidden(esk2_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( r2_hidden(esk2_4(X37,X38,X39,X40),X40)
        | esk2_4(X37,X38,X39,X40) = X37
        | esk2_4(X37,X38,X39,X40) = X38
        | esk2_4(X37,X38,X39,X40) = X39
        | X40 = k1_enumset1(X37,X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) = esk3_0
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0),esk3_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = esk3_0
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_29,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = esk3_0
    | r2_hidden(esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_28])).

cnf(c_0_31,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0) = esk4_0
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_36])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.39  # and selection function SelectNegativeLiterals.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.13/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.13/0.39  fof(c_0_8, negated_conjecture, ((k4_xboole_0(esk3_0,k1_tarski(esk4_0))!=esk3_0|r2_hidden(esk4_0,esk3_0))&(k4_xboole_0(esk3_0,k1_tarski(esk4_0))=esk3_0|~r2_hidden(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.39  fof(c_0_9, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_10, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_11, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  fof(c_0_12, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_13, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|k4_xboole_0(esk3_0,k1_tarski(esk4_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_20, plain, ![X31, X32, X33, X34, X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X35,X34)|(X35=X31|X35=X32|X35=X33)|X34!=k1_enumset1(X31,X32,X33))&(((X36!=X31|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33))&(X36!=X32|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33)))&(X36!=X33|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33))))&((((esk2_4(X37,X38,X39,X40)!=X37|~r2_hidden(esk2_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39))&(esk2_4(X37,X38,X39,X40)!=X38|~r2_hidden(esk2_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39)))&(esk2_4(X37,X38,X39,X40)!=X39|~r2_hidden(esk2_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39)))&(r2_hidden(esk2_4(X37,X38,X39,X40),X40)|(esk2_4(X37,X38,X39,X40)=X37|esk2_4(X37,X38,X39,X40)=X38|esk2_4(X37,X38,X39,X40)=X39)|X40=k1_enumset1(X37,X38,X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.13/0.39  cnf(c_0_21, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.39  cnf(c_0_23, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (k4_xboole_0(esk3_0,k1_tarski(esk4_0))=esk3_0|~r2_hidden(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_25, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_26, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0),esk3_0)|r2_hidden(esk4_0,esk3_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23])])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=esk3_0|~r2_hidden(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.39  cnf(c_0_29, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_18])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=esk3_0|r2_hidden(esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_28])).
% 0.13/0.39  cnf(c_0_31, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 0.13/0.39  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (esk1_3(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk3_0)=esk4_0|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.39  cnf(c_0_35, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_17])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 0.13/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_38, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_36])])).
% 0.13/0.39  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_37, c_0_18])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_42, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_36])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 44
% 0.13/0.39  # Proof object clause steps            : 29
% 0.13/0.39  # Proof object formula steps           : 15
% 0.13/0.39  # Proof object conjectures             : 15
% 0.13/0.39  # Proof object clause conjectures      : 12
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 11
% 0.13/0.39  # Proof object initial formulas used   : 7
% 0.13/0.39  # Proof object generating inferences   : 7
% 0.13/0.39  # Proof object simplifying inferences  : 24
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 15
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 30
% 0.13/0.39  # Removed in clause preprocessing      : 4
% 0.13/0.39  # Initial clauses in saturation        : 26
% 0.13/0.39  # Processed clauses                    : 185
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 82
% 0.13/0.39  # ...remaining for further processing  : 101
% 0.13/0.39  # Other redundant clauses eliminated   : 41
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 5
% 0.13/0.39  # Generated clauses                    : 646
% 0.13/0.39  # ...of the previous two non-trivial   : 599
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 602
% 0.13/0.39  # Factorizations                       : 6
% 0.13/0.39  # Equation resolutions                 : 41
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 61
% 0.13/0.39  #    Positive orientable unit clauses  : 15
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 45
% 0.13/0.39  # Current number of unprocessed clauses: 464
% 0.13/0.39  # ...number of literals in the above   : 1810
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 37
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1583
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 1277
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 85
% 0.13/0.39  # Unit Clause-clause subsumption calls : 8
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 17
% 0.13/0.39  # BW rewrite match successes           : 8
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 10823
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.040 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.045 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
