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
% DateTime   : Thu Dec  3 10:42:54 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 265 expanded)
%              Number of clauses        :   35 ( 107 expanded)
%              Number of leaves         :    8 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 470 expanded)
%              Number of equality atoms :   71 ( 339 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
        | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t69_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_xboole_0
    & k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X29,X30] :
      ( ( r2_hidden(esk3_2(X29,X30),X29)
        | X29 = k1_tarski(X30)
        | X29 = k1_xboole_0 )
      & ( esk3_2(X29,X30) != X30
        | X29 = k1_tarski(X30)
        | X29 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_23,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X16
        | X17 != k1_tarski(X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k1_tarski(X16) )
      & ( ~ r2_hidden(esk2_2(X20,X21),X21)
        | esk2_2(X20,X21) != X20
        | X21 = k1_tarski(X20) )
      & ( r2_hidden(esk2_2(X20,X21),X21)
        | esk2_2(X20,X21) = X20
        | X21 = k1_tarski(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_28,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),X1),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_17]),c_0_18]),c_0_20])).

cnf(c_0_34,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_17]),c_0_18]),c_0_20])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:38:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.46/0.67  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.46/0.67  # and selection function SelectNegativeLiterals.
% 0.46/0.67  #
% 0.46/0.67  # Preprocessing time       : 0.027 s
% 0.46/0.67  # Presaturation interreduction done
% 0.46/0.67  
% 0.46/0.67  # Proof found!
% 0.46/0.67  # SZS status Theorem
% 0.46/0.67  # SZS output start CNFRefutation
% 0.46/0.67  fof(t69_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 0.46/0.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.46/0.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.46/0.67  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.46/0.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.46/0.67  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.46/0.67  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.46/0.67  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.46/0.67  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t69_zfmisc_1])).
% 0.46/0.67  fof(c_0_9, negated_conjecture, (k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_xboole_0&k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.46/0.67  fof(c_0_10, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.46/0.67  fof(c_0_11, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.46/0.67  fof(c_0_12, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.46/0.67  fof(c_0_13, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.46/0.67  fof(c_0_14, plain, ![X29, X30]:((r2_hidden(esk3_2(X29,X30),X29)|(X29=k1_tarski(X30)|X29=k1_xboole_0))&(esk3_2(X29,X30)!=X30|(X29=k1_tarski(X30)|X29=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.46/0.67  fof(c_0_15, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.46/0.67  cnf(c_0_16, negated_conjecture, (k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.46/0.67  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.67  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.46/0.67  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.46/0.67  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.67  cnf(c_0_21, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.46/0.67  cnf(c_0_22, negated_conjecture, (k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.46/0.67  fof(c_0_23, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X18,X17)|X18=X16|X17!=k1_tarski(X16))&(X19!=X16|r2_hidden(X19,X17)|X17!=k1_tarski(X16)))&((~r2_hidden(esk2_2(X20,X21),X21)|esk2_2(X20,X21)!=X20|X21=k1_tarski(X20))&(r2_hidden(esk2_2(X20,X21),X21)|esk2_2(X20,X21)=X20|X21=k1_tarski(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.46/0.67  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.67  cnf(c_0_25, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.46/0.67  cnf(c_0_26, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_20])).
% 0.46/0.67  cnf(c_0_27, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_20])).
% 0.46/0.67  cnf(c_0_28, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.67  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.67  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.67  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_24, c_0_19])).
% 0.46/0.67  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),X1),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.46/0.67  cnf(c_0_33, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_17]), c_0_18]), c_0_20])).
% 0.46/0.67  cnf(c_0_34, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_29, c_0_19])).
% 0.46/0.67  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.67  cnf(c_0_36, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_19])).
% 0.46/0.67  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_31])).
% 0.46/0.67  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))), inference(er,[status(thm)],[c_0_32])).
% 0.46/0.67  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.67  cnf(c_0_40, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_33])).
% 0.46/0.67  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34])])).
% 0.46/0.67  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_17]), c_0_18]), c_0_20])).
% 0.46/0.67  cnf(c_0_43, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_36])).
% 0.46/0.67  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.46/0.67  cnf(c_0_45, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.46/0.67  cnf(c_0_46, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.46/0.67  cnf(c_0_47, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 0.46/0.67  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.46/0.67  cnf(c_0_49, negated_conjecture, (esk3_2(k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_40, c_0_44])).
% 0.46/0.67  cnf(c_0_50, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_25])).
% 0.46/0.67  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), ['proof']).
% 0.46/0.67  # SZS output end CNFRefutation
% 0.46/0.67  # Proof object total steps             : 52
% 0.46/0.67  # Proof object clause steps            : 35
% 0.46/0.67  # Proof object formula steps           : 17
% 0.46/0.67  # Proof object conjectures             : 16
% 0.46/0.67  # Proof object clause conjectures      : 13
% 0.46/0.67  # Proof object formula conjectures     : 3
% 0.46/0.67  # Proof object initial clauses used    : 13
% 0.46/0.67  # Proof object initial formulas used   : 8
% 0.46/0.67  # Proof object generating inferences   : 8
% 0.46/0.67  # Proof object simplifying inferences  : 39
% 0.46/0.67  # Training examples: 0 positive, 0 negative
% 0.46/0.67  # Parsed axioms                        : 8
% 0.46/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.67  # Initial clauses                      : 18
% 0.46/0.67  # Removed in clause preprocessing      : 4
% 0.46/0.67  # Initial clauses in saturation        : 14
% 0.46/0.67  # Processed clauses                    : 487
% 0.46/0.67  # ...of these trivial                  : 4
% 0.46/0.67  # ...subsumed                          : 170
% 0.46/0.67  # ...remaining for further processing  : 313
% 0.46/0.67  # Other redundant clauses eliminated   : 1276
% 0.46/0.67  # Clauses deleted for lack of memory   : 0
% 0.46/0.67  # Backward-subsumed                    : 3
% 0.46/0.67  # Backward-rewritten                   : 11
% 0.46/0.67  # Generated clauses                    : 34957
% 0.46/0.67  # ...of the previous two non-trivial   : 32060
% 0.46/0.67  # Contextual simplify-reflections      : 5
% 0.46/0.67  # Paramodulations                      : 33628
% 0.46/0.67  # Factorizations                       : 53
% 0.46/0.67  # Equation resolutions                 : 1277
% 0.46/0.67  # Propositional unsat checks           : 0
% 0.46/0.67  #    Propositional check models        : 0
% 0.46/0.67  #    Propositional check unsatisfiable : 0
% 0.46/0.67  #    Propositional clauses             : 0
% 0.46/0.67  #    Propositional clauses after purity: 0
% 0.46/0.67  #    Propositional unsat core size     : 0
% 0.46/0.67  #    Propositional preprocessing time  : 0.000
% 0.46/0.67  #    Propositional encoding time       : 0.000
% 0.46/0.67  #    Propositional solver time         : 0.000
% 0.46/0.67  #    Success case prop preproc time    : 0.000
% 0.46/0.67  #    Success case prop encoding time   : 0.000
% 0.46/0.67  #    Success case prop solver time     : 0.000
% 0.46/0.67  # Current number of processed clauses  : 280
% 0.46/0.67  #    Positive orientable unit clauses  : 5
% 0.46/0.67  #    Positive unorientable unit clauses: 0
% 0.46/0.67  #    Negative unit clauses             : 2
% 0.46/0.67  #    Non-unit-clauses                  : 273
% 0.46/0.67  # Current number of unprocessed clauses: 31577
% 0.46/0.67  # ...number of literals in the above   : 182156
% 0.46/0.67  # Current number of archived formulas  : 0
% 0.46/0.67  # Current number of archived clauses   : 32
% 0.46/0.67  # Clause-clause subsumption calls (NU) : 8442
% 0.46/0.67  # Rec. Clause-clause subsumption calls : 2505
% 0.46/0.67  # Non-unit clause-clause subsumptions  : 168
% 0.46/0.67  # Unit Clause-clause subsumption calls : 77
% 0.46/0.67  # Rewrite failures with RHS unbound    : 0
% 0.46/0.67  # BW rewrite match attempts            : 5
% 0.46/0.67  # BW rewrite match successes           : 3
% 0.46/0.67  # Condensation attempts                : 0
% 0.46/0.67  # Condensation successes               : 0
% 0.46/0.67  # Termbank termtop insertions          : 725324
% 0.46/0.67  
% 0.46/0.67  # -------------------------------------------------
% 0.46/0.67  # User time                : 0.323 s
% 0.46/0.67  # System time              : 0.018 s
% 0.46/0.67  # Total time               : 0.341 s
% 0.46/0.67  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
