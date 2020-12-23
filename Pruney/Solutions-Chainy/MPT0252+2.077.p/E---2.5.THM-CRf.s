%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 109 expanded)
%              Number of clauses        :   29 (  47 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 214 expanded)
%              Number of equality atoms :   58 ( 133 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t47_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X33,X34] : k3_tarski(k2_tarski(X33,X34)) = k2_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X8
        | X12 = X9
        | X12 = X10
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( X13 != X8
        | r2_hidden(X13,X11)
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( esk1_4(X14,X15,X16,X17) != X14
        | ~ r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | X17 = k1_enumset1(X14,X15,X16) )
      & ( esk1_4(X14,X15,X16,X17) != X15
        | ~ r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | X17 = k1_enumset1(X14,X15,X16) )
      & ( esk1_4(X14,X15,X16,X17) != X16
        | ~ r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | X17 = k1_enumset1(X14,X15,X16) )
      & ( r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | esk1_4(X14,X15,X16,X17) = X14
        | esk1_4(X14,X15,X16,X17) = X15
        | esk1_4(X14,X15,X16,X17) = X16
        | X17 = k1_enumset1(X14,X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_14,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0),esk4_0)
    & ~ r2_hidden(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X19,X20,X21] : k1_enumset1(X19,X20,X21) = k1_enumset1(X21,X20,X19) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_21]),c_0_22])).

fof(c_0_29,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_25]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_21]),c_0_22]),c_0_22])).

fof(c_0_32,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | r1_tarski(X31,k3_tarski(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X1,X1,X1,X3,X4) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X35,X36,X37] :
      ( ( r2_hidden(X35,X37)
        | ~ r1_tarski(k2_tarski(X35,X36),X37) )
      & ( r2_hidden(X36,X37)
        | ~ r1_tarski(k2_tarski(X35,X36),X37) )
      & ( ~ r2_hidden(X35,X37)
        | ~ r2_hidden(X36,X37)
        | r1_tarski(k2_tarski(X35,X36),X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))) = esk4_0
    | ~ r1_tarski(esk4_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_18]),c_0_21]),c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.38  # and selection function SelectNegativeLiterals.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t47_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 0.20/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.20/0.38  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t47_zfmisc_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X33, X34]:k3_tarski(k2_tarski(X33,X34))=k2_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.38  fof(c_0_12, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_13, plain, ![X8, X9, X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X12,X11)|(X12=X8|X12=X9|X12=X10)|X11!=k1_enumset1(X8,X9,X10))&(((X13!=X8|r2_hidden(X13,X11)|X11!=k1_enumset1(X8,X9,X10))&(X13!=X9|r2_hidden(X13,X11)|X11!=k1_enumset1(X8,X9,X10)))&(X13!=X10|r2_hidden(X13,X11)|X11!=k1_enumset1(X8,X9,X10))))&((((esk1_4(X14,X15,X16,X17)!=X14|~r2_hidden(esk1_4(X14,X15,X16,X17),X17)|X17=k1_enumset1(X14,X15,X16))&(esk1_4(X14,X15,X16,X17)!=X15|~r2_hidden(esk1_4(X14,X15,X16,X17),X17)|X17=k1_enumset1(X14,X15,X16)))&(esk1_4(X14,X15,X16,X17)!=X16|~r2_hidden(esk1_4(X14,X15,X16,X17),X17)|X17=k1_enumset1(X14,X15,X16)))&(r2_hidden(esk1_4(X14,X15,X16,X17),X17)|(esk1_4(X14,X15,X16,X17)=X14|esk1_4(X14,X15,X16,X17)=X15|esk1_4(X14,X15,X16,X17)=X16)|X17=k1_enumset1(X14,X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_15, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_16, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0),esk4_0)&~r2_hidden(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.38  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_19, plain, ![X19, X20, X21]:k1_enumset1(X19,X20,X21)=k1_enumset1(X21,X20,X19), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_25, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_26, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_21]), c_0_22])).
% 0.20/0.38  fof(c_0_29, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_18]), c_0_25]), c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.20/0.38  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.20/0.38  fof(c_0_32, plain, ![X31, X32]:(~r2_hidden(X31,X32)|r1_tarski(X31,k3_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.20/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X1,X1,X1,X3,X4)), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.38  cnf(c_0_37, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_38, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.38  fof(c_0_39, plain, ![X35, X36, X37]:(((r2_hidden(X35,X37)|~r1_tarski(k2_tarski(X35,X36),X37))&(r2_hidden(X36,X37)|~r1_tarski(k2_tarski(X35,X36),X37)))&(~r2_hidden(X35,X37)|~r2_hidden(X36,X37)|r1_tarski(k2_tarski(X35,X36),X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_40, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)))=esk4_0|~r1_tarski(esk4_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_42, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_44, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X3,X1)))), inference(spm,[status(thm)],[c_0_37, c_0_40])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.20/0.38  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_18]), c_0_21]), c_0_22])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 50
% 0.20/0.38  # Proof object clause steps            : 29
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 11
% 0.20/0.38  # Proof object clause conjectures      : 8
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 7
% 0.20/0.38  # Proof object simplifying inferences  : 27
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 22
% 0.20/0.38  # Removed in clause preprocessing      : 4
% 0.20/0.38  # Initial clauses in saturation        : 18
% 0.20/0.38  # Processed clauses                    : 58
% 0.20/0.38  # ...of these trivial                  : 5
% 0.20/0.38  # ...subsumed                          : 16
% 0.20/0.38  # ...remaining for further processing  : 37
% 0.20/0.38  # Other redundant clauses eliminated   : 9
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 5
% 0.20/0.38  # Generated clauses                    : 171
% 0.20/0.38  # ...of the previous two non-trivial   : 153
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 158
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 13
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 27
% 0.20/0.38  #    Positive orientable unit clauses  : 9
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 16
% 0.20/0.38  # Current number of unprocessed clauses: 103
% 0.20/0.38  # ...number of literals in the above   : 461
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 9
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 89
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 87
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 16
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 31
% 0.20/0.38  # BW rewrite match successes           : 12
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2852
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.033 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
