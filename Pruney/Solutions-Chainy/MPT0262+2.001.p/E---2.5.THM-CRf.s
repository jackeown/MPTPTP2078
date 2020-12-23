%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:55 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 133 expanded)
%              Number of clauses        :   33 (  58 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 407 expanded)
%              Number of equality atoms :   67 ( 174 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

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

fof(t57_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_9,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X14
        | X18 = X15
        | X18 = X16
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X14
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( esk2_4(X20,X21,X22,X23) != X20
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X20,X21,X22,X23) != X21
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X20,X21,X22,X23) != X22
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | esk2_4(X20,X21,X22,X23) = X20
        | esk2_4(X20,X21,X22,X23) = X21
        | esk2_4(X20,X21,X22,X23) = X22
        | X23 = k1_enumset1(X20,X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_11,plain,(
    ! [X30,X31,X32,X33] : k3_enumset1(X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_12,plain,(
    ! [X34,X35,X36,X37,X38] : k4_enumset1(X34,X34,X35,X36,X37,X38) = k3_enumset1(X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_13,plain,(
    ! [X39,X40,X41,X42,X43,X44] : k5_enumset1(X39,X39,X40,X41,X42,X43,X44) = k4_enumset1(X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_14,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] : k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51) = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_15,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

fof(c_0_23,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_29,plain,
    ( esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) = X4
    | esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) = X3
    | esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) = X2
    | r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3)) = X2
    | esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3)) = X3
    | r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_29])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,esk1_2(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = X2
    | esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = X3
    | r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_29])])).

cnf(c_0_35,plain,
    ( esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = X2
    | r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_32])])).

cnf(c_0_36,plain,
    ( esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = X2
    | r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | ~ r1_xboole_0(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X3,X2)
          & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t57_zfmisc_1])).

cnf(c_0_39,plain,
    ( esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = X2
    | r2_hidden(X3,X1)
    | r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    & ~ r2_hidden(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).

fof(c_0_41,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X4)
    | ~ r2_hidden(esk1_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X4),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:30:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 2.14/2.30  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 2.14/2.30  # and selection function GSelectMinInfpos.
% 2.14/2.30  #
% 2.14/2.30  # Preprocessing time       : 0.027 s
% 2.14/2.30  # Presaturation interreduction done
% 2.14/2.30  
% 2.14/2.30  # Proof found!
% 2.14/2.30  # SZS status Theorem
% 2.14/2.30  # SZS output start CNFRefutation
% 2.14/2.30  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.14/2.30  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.14/2.30  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.14/2.30  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.14/2.30  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.14/2.30  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.14/2.30  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.14/2.30  fof(t57_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.14/2.30  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.14/2.30  fof(c_0_9, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X18,X17)|(X18=X14|X18=X15|X18=X16)|X17!=k1_enumset1(X14,X15,X16))&(((X19!=X14|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))&(X19!=X15|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16)))&(X19!=X16|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))))&((((esk2_4(X20,X21,X22,X23)!=X20|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22))&(esk2_4(X20,X21,X22,X23)!=X21|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(esk2_4(X20,X21,X22,X23)!=X22|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(r2_hidden(esk2_4(X20,X21,X22,X23),X23)|(esk2_4(X20,X21,X22,X23)=X20|esk2_4(X20,X21,X22,X23)=X21|esk2_4(X20,X21,X22,X23)=X22)|X23=k1_enumset1(X20,X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 2.14/2.30  fof(c_0_10, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.14/2.30  fof(c_0_11, plain, ![X30, X31, X32, X33]:k3_enumset1(X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.14/2.30  fof(c_0_12, plain, ![X34, X35, X36, X37, X38]:k4_enumset1(X34,X34,X35,X36,X37,X38)=k3_enumset1(X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.14/2.30  fof(c_0_13, plain, ![X39, X40, X41, X42, X43, X44]:k5_enumset1(X39,X39,X40,X41,X42,X43,X44)=k4_enumset1(X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 2.14/2.30  fof(c_0_14, plain, ![X45, X46, X47, X48, X49, X50, X51]:k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51)=k5_enumset1(X45,X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 2.14/2.30  cnf(c_0_15, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.14/2.30  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.14/2.30  cnf(c_0_17, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.14/2.30  cnf(c_0_18, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.14/2.30  cnf(c_0_19, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.14/2.30  cnf(c_0_20, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.14/2.30  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.14/2.30  cnf(c_0_22, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 2.14/2.30  fof(c_0_23, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 2.14/2.30  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 2.14/2.30  cnf(c_0_25, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_22])).
% 2.14/2.30  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.14/2.30  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.14/2.30  cnf(c_0_28, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 2.14/2.30  cnf(c_0_29, plain, (esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))=X4|esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))=X3|esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))=X2|r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 2.14/2.30  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.14/2.30  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.14/2.30  cnf(c_0_32, plain, (esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3))=X2|esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3))=X3|r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X3))), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_29])])).
% 2.14/2.30  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,esk1_2(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.14/2.30  cnf(c_0_34, plain, (esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))=X2|esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))=X3|r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_29])])).
% 2.14/2.30  cnf(c_0_35, plain, (esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))=X2|r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_32])])).
% 2.14/2.30  cnf(c_0_36, plain, (esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))=X2|r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))|~r1_xboole_0(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.14/2.30  cnf(c_0_37, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_31, c_0_35])).
% 2.14/2.30  fof(c_0_38, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2))))), inference(assume_negation,[status(cth)],[t57_zfmisc_1])).
% 2.14/2.30  cnf(c_0_39, plain, (esk1_2(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))=X2|r2_hidden(X3,X1)|r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 2.14/2.30  fof(c_0_40, negated_conjecture, ((~r2_hidden(esk3_0,esk4_0)&~r2_hidden(esk5_0,esk4_0))&~r1_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).
% 2.14/2.30  fof(c_0_41, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.14/2.30  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 2.14/2.30  cnf(c_0_43, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))), inference(spm,[status(thm)],[c_0_31, c_0_39])).
% 2.14/2.30  cnf(c_0_44, negated_conjecture, (~r1_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.14/2.30  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.14/2.30  cnf(c_0_46, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X4)|~r2_hidden(esk1_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X4),X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.14/2.30  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 2.14/2.30  cnf(c_0_48, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2)), inference(spm,[status(thm)],[c_0_46, c_0_26])).
% 2.14/2.30  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.14/2.30  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.14/2.30  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), ['proof']).
% 2.14/2.30  # SZS output end CNFRefutation
% 2.14/2.30  # Proof object total steps             : 52
% 2.14/2.30  # Proof object clause steps            : 33
% 2.14/2.30  # Proof object formula steps           : 19
% 2.14/2.30  # Proof object conjectures             : 8
% 2.14/2.30  # Proof object clause conjectures      : 5
% 2.14/2.30  # Proof object formula conjectures     : 3
% 2.14/2.30  # Proof object initial clauses used    : 14
% 2.14/2.30  # Proof object initial formulas used   : 9
% 2.14/2.30  # Proof object generating inferences   : 14
% 2.14/2.30  # Proof object simplifying inferences  : 24
% 2.14/2.30  # Training examples: 0 positive, 0 negative
% 2.14/2.30  # Parsed axioms                        : 9
% 2.14/2.30  # Removed by relevancy pruning/SinE    : 0
% 2.14/2.30  # Initial clauses                      : 20
% 2.14/2.30  # Removed in clause preprocessing      : 6
% 2.14/2.30  # Initial clauses in saturation        : 14
% 2.14/2.30  # Processed clauses                    : 1298
% 2.14/2.30  # ...of these trivial                  : 6
% 2.14/2.30  # ...subsumed                          : 770
% 2.14/2.30  # ...remaining for further processing  : 522
% 2.14/2.30  # Other redundant clauses eliminated   : 582
% 2.14/2.30  # Clauses deleted for lack of memory   : 0
% 2.14/2.30  # Backward-subsumed                    : 3
% 2.14/2.30  # Backward-rewritten                   : 0
% 2.14/2.30  # Generated clauses                    : 46902
% 2.14/2.30  # ...of the previous two non-trivial   : 44780
% 2.14/2.30  # Contextual simplify-reflections      : 9
% 2.14/2.30  # Paramodulations                      : 45862
% 2.14/2.30  # Factorizations                       : 461
% 2.14/2.30  # Equation resolutions                 : 582
% 2.14/2.30  # Propositional unsat checks           : 0
% 2.14/2.30  #    Propositional check models        : 0
% 2.14/2.30  #    Propositional check unsatisfiable : 0
% 2.14/2.30  #    Propositional clauses             : 0
% 2.14/2.30  #    Propositional clauses after purity: 0
% 2.14/2.30  #    Propositional unsat core size     : 0
% 2.14/2.30  #    Propositional preprocessing time  : 0.000
% 2.14/2.30  #    Propositional encoding time       : 0.000
% 2.14/2.30  #    Propositional solver time         : 0.000
% 2.14/2.30  #    Success case prop preproc time    : 0.000
% 2.14/2.30  #    Success case prop encoding time   : 0.000
% 2.14/2.30  #    Success case prop solver time     : 0.000
% 2.14/2.30  # Current number of processed clauses  : 501
% 2.14/2.30  #    Positive orientable unit clauses  : 3
% 2.14/2.30  #    Positive unorientable unit clauses: 0
% 2.14/2.30  #    Negative unit clauses             : 12
% 2.14/2.30  #    Non-unit-clauses                  : 486
% 2.14/2.30  # Current number of unprocessed clauses: 43300
% 2.14/2.30  # ...number of literals in the above   : 512620
% 2.14/2.30  # Current number of archived formulas  : 0
% 2.14/2.30  # Current number of archived clauses   : 23
% 2.14/2.30  # Clause-clause subsumption calls (NU) : 38631
% 2.14/2.30  # Rec. Clause-clause subsumption calls : 10873
% 2.14/2.30  # Non-unit clause-clause subsumptions  : 717
% 2.14/2.30  # Unit Clause-clause subsumption calls : 36
% 2.14/2.30  # Rewrite failures with RHS unbound    : 0
% 2.14/2.30  # BW rewrite match attempts            : 6
% 2.14/2.30  # BW rewrite match successes           : 0
% 2.14/2.30  # Condensation attempts                : 0
% 2.14/2.30  # Condensation successes               : 0
% 2.14/2.30  # Termbank termtop insertions          : 1391663
% 2.14/2.30  
% 2.14/2.30  # -------------------------------------------------
% 2.14/2.30  # User time                : 1.924 s
% 2.14/2.30  # System time              : 0.031 s
% 2.14/2.30  # Total time               : 1.955 s
% 2.14/2.30  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
