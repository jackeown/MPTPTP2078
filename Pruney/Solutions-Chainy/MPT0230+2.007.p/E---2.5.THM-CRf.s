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
% DateTime   : Thu Dec  3 10:38:31 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 102 expanded)
%              Number of clauses        :   24 (  41 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 189 expanded)
%              Number of equality atoms :   87 ( 150 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
          & X1 != X2
          & X1 != X3 ) ),
    inference(assume_negation,[status(cth)],[t25_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X10
        | X14 = X11
        | X14 = X12
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X10
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( esk1_4(X16,X17,X18,X19) != X16
        | ~ r2_hidden(esk1_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( esk1_4(X16,X17,X18,X19) != X17
        | ~ r2_hidden(esk1_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( esk1_4(X16,X17,X18,X19) != X18
        | ~ r2_hidden(esk1_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( r2_hidden(esk1_4(X16,X17,X18,X19),X19)
        | esk1_4(X16,X17,X18,X19) = X16
        | esk1_4(X16,X17,X18,X19) = X17
        | esk1_4(X16,X17,X18,X19) = X18
        | X19 = k1_enumset1(X16,X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_12,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))
    & esk3_0 != esk4_0
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_15,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X30,X31,X32] : k1_enumset1(X30,X31,X32) = k2_xboole_0(k2_tarski(X30,X31),k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X21
        | X24 = X22
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( esk2_3(X26,X27,X28) != X26
        | ~ r2_hidden(esk2_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( esk2_3(X26,X27,X28) != X27
        | ~ r2_hidden(esk2_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( r2_hidden(esk2_3(X26,X27,X28),X28)
        | esk2_3(X26,X27,X28) = X26
        | esk2_3(X26,X27,X28) = X27
        | X28 = k2_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23]),c_0_24]),c_0_24]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(X2,X2,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_24]),c_0_19]),c_0_20])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk5_0,esk3_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.41  # and selection function SelectNegativeLiterals.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.027 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t25_zfmisc_1, conjecture, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 0.19/0.41  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.19/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.41  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.41  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t25_zfmisc_1])).
% 0.19/0.41  fof(c_0_11, plain, ![X10, X11, X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X14,X13)|(X14=X10|X14=X11|X14=X12)|X13!=k1_enumset1(X10,X11,X12))&(((X15!=X10|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12))&(X15!=X11|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12)))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12))))&((((esk1_4(X16,X17,X18,X19)!=X16|~r2_hidden(esk1_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18))&(esk1_4(X16,X17,X18,X19)!=X17|~r2_hidden(esk1_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18)))&(esk1_4(X16,X17,X18,X19)!=X18|~r2_hidden(esk1_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18)))&(r2_hidden(esk1_4(X16,X17,X18,X19),X19)|(esk1_4(X16,X17,X18,X19)=X16|esk1_4(X16,X17,X18,X19)=X17|esk1_4(X16,X17,X18,X19)=X18)|X19=k1_enumset1(X16,X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.41  fof(c_0_12, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  fof(c_0_13, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.41  fof(c_0_14, negated_conjecture, ((r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))&esk3_0!=esk4_0)&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.41  fof(c_0_15, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_16, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_17, plain, ![X30, X31, X32]:k1_enumset1(X30,X31,X32)=k2_xboole_0(k2_tarski(X30,X31),k1_tarski(X32)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.19/0.41  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_20, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_21, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  fof(c_0_25, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.41  cnf(c_0_26, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_27, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X24,X23)|(X24=X21|X24=X22)|X23!=k2_tarski(X21,X22))&((X25!=X21|r2_hidden(X25,X23)|X23!=k2_tarski(X21,X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k2_tarski(X21,X22))))&(((esk2_3(X26,X27,X28)!=X26|~r2_hidden(esk2_3(X26,X27,X28),X28)|X28=k2_tarski(X26,X27))&(esk2_3(X26,X27,X28)!=X27|~r2_hidden(esk2_3(X26,X27,X28),X28)|X28=k2_tarski(X26,X27)))&(r2_hidden(esk2_3(X26,X27,X28),X28)|(esk2_3(X26,X27,X28)=X26|esk2_3(X26,X27,X28)=X27)|X28=k2_tarski(X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.41  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24]), c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.19/0.41  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23]), c_0_24]), c_0_24]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.19/0.41  cnf(c_0_33, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.41  cnf(c_0_36, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X3))=k3_enumset1(X2,X2,X2,X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_37, plain, (X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_24]), c_0_19]), c_0_20])).
% 0.19/0.41  cnf(c_0_38, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk5_0,esk3_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.41  cnf(c_0_40, plain, (X1=X2|X1=X3|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 45
% 0.19/0.41  # Proof object clause steps            : 24
% 0.19/0.41  # Proof object formula steps           : 21
% 0.19/0.41  # Proof object conjectures             : 11
% 0.19/0.41  # Proof object clause conjectures      : 8
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 12
% 0.19/0.41  # Proof object initial formulas used   : 10
% 0.19/0.41  # Proof object generating inferences   : 6
% 0.19/0.41  # Proof object simplifying inferences  : 25
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 10
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 24
% 0.19/0.41  # Removed in clause preprocessing      : 4
% 0.19/0.41  # Initial clauses in saturation        : 20
% 0.19/0.41  # Processed clauses                    : 78
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 22
% 0.19/0.41  # ...remaining for further processing  : 56
% 0.19/0.41  # Other redundant clauses eliminated   : 56
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 1
% 0.19/0.41  # Generated clauses                    : 966
% 0.19/0.41  # ...of the previous two non-trivial   : 856
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 888
% 0.19/0.41  # Factorizations                       : 10
% 0.19/0.41  # Equation resolutions                 : 68
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 50
% 0.19/0.41  #    Positive orientable unit clauses  : 8
% 0.19/0.41  #    Positive unorientable unit clauses: 1
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 39
% 0.19/0.41  # Current number of unprocessed clauses: 795
% 0.19/0.41  # ...number of literals in the above   : 6345
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 5
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 248
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 141
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 22
% 0.19/0.41  # Unit Clause-clause subsumption calls : 26
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 9
% 0.19/0.41  # BW rewrite match successes           : 3
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 18767
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.061 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.066 s
% 0.19/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
