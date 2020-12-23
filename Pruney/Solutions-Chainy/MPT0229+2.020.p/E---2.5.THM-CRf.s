%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:29 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 245 expanded)
%              Number of clauses        :   30 (  99 expanded)
%              Number of leaves         :   10 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 405 expanded)
%              Number of equality atoms :   60 ( 299 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t24_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X36,X37] :
      ( ( ~ r1_tarski(X36,k1_tarski(X37))
        | X36 = k1_xboole_0
        | X36 = k1_tarski(X37) )
      & ( X36 != k1_xboole_0
        | r1_tarski(X36,k1_tarski(X37)) )
      & ( X36 != k1_tarski(X37)
        | r1_tarski(X36,k1_tarski(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X32,X33,X34,X35] : k3_enumset1(X32,X32,X33,X34,X35) = k2_enumset1(X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X21,X20)
        | X21 = X19
        | X20 != k1_tarski(X19) )
      & ( X22 != X19
        | r2_hidden(X22,X20)
        | X20 != k1_tarski(X19) )
      & ( ~ r2_hidden(esk3_2(X23,X24),X24)
        | esk3_2(X23,X24) != X23
        | X24 = k1_tarski(X23) )
      & ( r2_hidden(esk3_2(X23,X24),X24)
        | esk3_2(X23,X24) = X23
        | X24 = k1_tarski(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0))
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
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
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( ( ~ r1_xboole_0(X17,X18)
        | k4_xboole_0(X17,X18) = X17 )
      & ( k4_xboole_0(X17,X18) != X17
        | r1_xboole_0(X17,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_43,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk2_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk2_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_48,c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.20/0.37  # and selection function SelectCQIArNpEqFirst.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t24_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 0.20/0.37  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2)), inference(assume_negation,[status(cth)],[t24_zfmisc_1])).
% 0.20/0.37  fof(c_0_11, plain, ![X36, X37]:((~r1_tarski(X36,k1_tarski(X37))|(X36=k1_xboole_0|X36=k1_tarski(X37)))&((X36!=k1_xboole_0|r1_tarski(X36,k1_tarski(X37)))&(X36!=k1_tarski(X37)|r1_tarski(X36,k1_tarski(X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.37  fof(c_0_12, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.37  fof(c_0_13, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.37  fof(c_0_14, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.37  fof(c_0_15, plain, ![X32, X33, X34, X35]:k3_enumset1(X32,X32,X33,X34,X35)=k2_enumset1(X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.37  fof(c_0_16, plain, ![X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X21,X20)|X21=X19|X20!=k1_tarski(X19))&(X22!=X19|r2_hidden(X22,X20)|X20!=k1_tarski(X19)))&((~r2_hidden(esk3_2(X23,X24),X24)|esk3_2(X23,X24)!=X23|X24=k1_tarski(X23))&(r2_hidden(esk3_2(X23,X24),X24)|esk3_2(X23,X24)=X23|X24=k1_tarski(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.37  fof(c_0_17, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0))&esk4_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.37  cnf(c_0_18, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_24, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  fof(c_0_26, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.37  cnf(c_0_27, plain, (r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.37  cnf(c_0_28, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.37  cnf(c_0_30, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.20/0.37  fof(c_0_32, plain, ![X17, X18]:((~r1_xboole_0(X17,X18)|k4_xboole_0(X17,X18)=X17)&(k4_xboole_0(X17,X18)!=X17|r1_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.37  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.37  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_35, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.37  cnf(c_0_36, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.37  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.37  cnf(c_0_39, plain, (k4_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.37  cnf(c_0_40, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.37  cnf(c_0_42, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  fof(c_0_43, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk2_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk2_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.37  cnf(c_0_44, plain, (r1_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.20/0.37  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_45])).
% 0.20/0.37  cnf(c_0_49, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.37  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_48, c_0_49]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 51
% 0.20/0.37  # Proof object clause steps            : 30
% 0.20/0.37  # Proof object formula steps           : 21
% 0.20/0.37  # Proof object conjectures             : 13
% 0.20/0.37  # Proof object clause conjectures      : 10
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 13
% 0.20/0.37  # Proof object initial formulas used   : 10
% 0.20/0.37  # Proof object generating inferences   : 8
% 0.20/0.37  # Proof object simplifying inferences  : 34
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 11
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 22
% 0.20/0.37  # Removed in clause preprocessing      : 4
% 0.20/0.37  # Initial clauses in saturation        : 18
% 0.20/0.37  # Processed clauses                    : 56
% 0.20/0.37  # ...of these trivial                  : 1
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 55
% 0.20/0.37  # Other redundant clauses eliminated   : 8
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 5
% 0.20/0.37  # Generated clauses                    : 95
% 0.20/0.37  # ...of the previous two non-trivial   : 75
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 87
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 8
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 27
% 0.20/0.37  #    Positive orientable unit clauses  : 8
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 17
% 0.20/0.37  # Current number of unprocessed clauses: 55
% 0.20/0.37  # ...number of literals in the above   : 169
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 28
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 21
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 19
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 6
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 5
% 0.20/0.37  # BW rewrite match successes           : 1
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 2177
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.029 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.033 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
