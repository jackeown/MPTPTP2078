%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 678 expanded)
%              Number of clauses        :   30 ( 307 expanded)
%              Number of leaves         :    7 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 (2330 expanded)
%              Number of equality atoms :  132 (1912 expanded)
%              Maximal formula depth    :   52 (   5 average)
%              Maximal clause size      :   76 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t9_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X2 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(d7_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( X10 = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X11 != X1
              & X11 != X2
              & X11 != X3
              & X11 != X4
              & X11 != X5
              & X11 != X6
              & X11 != X7
              & X11 != X8
              & X11 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(t129_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(t96_enumset1,axiom,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_7,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50,X51] : k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) = k2_xboole_0(k2_tarski(X44,X45),k4_enumset1(X46,X47,X48,X49,X50,X51)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

fof(c_0_8,plain,(
    ! [X53,X54] : k1_enumset1(X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k1_tarski(X1) = k2_tarski(X2,X3)
       => X2 = X3 ) ),
    inference(assume_negation,[status(cth)],[t9_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X12
        | X22 = X13
        | X22 = X14
        | X22 = X15
        | X22 = X16
        | X22 = X17
        | X22 = X18
        | X22 = X19
        | X22 = X20
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X12
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X13
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X14
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X15
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X16
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X17
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X18
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X24
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X25
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X26
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X27
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X28
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X29
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) )
      & ( r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X24
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X25
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X26
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X27
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X28
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X29
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X30
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X31
        | esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33) = X32
        | X33 = k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

fof(c_0_11,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42,X43] : k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) = k2_xboole_0(k1_enumset1(X35,X36,X37),k4_enumset1(X38,X39,X40,X41,X42,X43)) ),
    inference(variable_rename,[status(thm)],[t129_enumset1])).

fof(c_0_12,plain,(
    ! [X55] : k6_enumset1(X55,X55,X55,X55,X55,X55,X55,X55) = k1_tarski(X55) ),
    inference(variable_rename,[status(thm)],[t96_enumset1])).

fof(c_0_13,plain,(
    ! [X52] : k2_tarski(X52,X52) = k1_tarski(X52) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_14,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_tarski(esk3_0,esk4_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_17,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | X1 = X10
    | X1 = X11
    | ~ r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X2,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( X1 = X11
    | X1 = X10
    | X1 = X9
    | X1 = X8
    | X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_xboole_0(k1_enumset1(X3,X4,X5),k4_enumset1(X6,X7,X8,X9,X10,X11))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1)) = k1_enumset1(X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_15]),c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_xboole_0(k1_enumset1(X4,X5,X2),k4_enumset1(X6,X7,X8,X9,X10,X11)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) = k1_enumset1(esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_15]),c_0_15])).

cnf(c_0_28,plain,
    ( X1 = X2
    | X3 != k1_enumset1(X2,X2,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_xboole_0(k1_enumset1(X3,X4,X1),k4_enumset1(X5,X6,X7,X8,X9,X10)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | X1 != k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X2,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk2_0
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_xboole_0(k1_enumset1(X4,X2,X5),k4_enumset1(X6,X7,X8,X9,X10,X11)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_xboole_0(k1_enumset1(X3,X1,X4),k4_enumset1(X5,X6,X7,X8,X9,X10)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | X1 != k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.37  # and selection function SelectNegativeLiterals.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t9_zfmisc_1, conjecture, ![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X2=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 0.19/0.37  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 0.19/0.37  fof(t129_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 0.19/0.37  fof(t96_enumset1, axiom, ![X1]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_enumset1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(c_0_7, plain, ![X44, X45, X46, X47, X48, X49, X50, X51]:k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)=k2_xboole_0(k2_tarski(X44,X45),k4_enumset1(X46,X47,X48,X49,X50,X51)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.19/0.37  fof(c_0_8, plain, ![X53, X54]:k1_enumset1(X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X2=X3)), inference(assume_negation,[status(cth)],[t9_zfmisc_1])).
% 0.19/0.37  fof(c_0_10, plain, ![X12, X13, X14, X15, X16, X17, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X22,X21)|(X22=X12|X22=X13|X22=X14|X22=X15|X22=X16|X22=X17|X22=X18|X22=X19|X22=X20)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20))&(((((((((X23!=X12|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20))&(X23!=X13|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20)))&(X23!=X14|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20)))&(X23!=X15|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20)))&(X23!=X16|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20)))&(X23!=X17|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20)))&(X23!=X18|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20)))&(X23!=X19|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20)))&(X23!=X20|r2_hidden(X23,X21)|X21!=k7_enumset1(X12,X13,X14,X15,X16,X17,X18,X19,X20))))&((((((((((esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X24|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X25|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X26|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X27|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X28|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X29|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X30|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X31|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)!=X32|~r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))&(r2_hidden(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33),X33)|(esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X24|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X25|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X26|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X27|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X28|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X29|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X30|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X31|esk1_10(X24,X25,X26,X27,X28,X29,X30,X31,X32,X33)=X32)|X33=k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X35, X36, X37, X38, X39, X40, X41, X42, X43]:k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)=k2_xboole_0(k1_enumset1(X35,X36,X37),k4_enumset1(X38,X39,X40,X41,X42,X43)), inference(variable_rename,[status(thm)],[t129_enumset1])).
% 0.19/0.37  fof(c_0_12, plain, ![X55]:k6_enumset1(X55,X55,X55,X55,X55,X55,X55,X55)=k1_tarski(X55), inference(variable_rename,[status(thm)],[t96_enumset1])).
% 0.19/0.37  fof(c_0_13, plain, ![X52]:k2_tarski(X52,X52)=k1_tarski(X52), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  cnf(c_0_14, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  fof(c_0_16, negated_conjecture, (k1_tarski(esk2_0)=k2_tarski(esk3_0,esk4_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.37  cnf(c_0_17, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|X1=X9|X1=X10|X1=X11|~r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_18, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_19, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_21, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X2,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k1_tarski(esk2_0)=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_24, plain, (X1=X11|X1=X10|X1=X9|X1=X8|X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k2_xboole_0(k1_enumset1(X3,X4,X5),k4_enumset1(X6,X7,X8,X9,X10,X11))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  cnf(c_0_25, plain, (k2_xboole_0(k1_enumset1(X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1))=k1_enumset1(X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_15]), c_0_21])).
% 0.19/0.37  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_xboole_0(k1_enumset1(X4,X5,X2),k4_enumset1(X6,X7,X8,X9,X10,X11))), inference(rw,[status(thm)],[c_0_22, c_0_18])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)=k1_enumset1(esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_15]), c_0_15])).
% 0.19/0.37  cnf(c_0_28, plain, (X1=X2|X3!=k1_enumset1(X2,X2,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X2!=k2_xboole_0(k1_enumset1(X3,X4,X1),k4_enumset1(X5,X6,X7,X8,X9,X10))), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_27])).
% 0.19/0.37  cnf(c_0_31, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,X1)|X1!=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X2,X5,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (X1=esk2_0|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_xboole_0(k1_enumset1(X4,X2,X5),k4_enumset1(X6,X7,X8,X9,X10,X11))), inference(rw,[status(thm)],[c_0_33, c_0_18])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (esk2_0=esk4_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_38, plain, (r2_hidden(X1,X2)|X2!=k2_xboole_0(k1_enumset1(X3,X1,X4),k4_enumset1(X5,X6,X7,X8,X9,X10))), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (k2_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_0,X1)|X1!=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_34, c_0_37])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 45
% 0.19/0.37  # Proof object clause steps            : 30
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 16
% 0.19/0.37  # Proof object clause conjectures      : 13
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 10
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 10
% 0.19/0.37  # Proof object simplifying inferences  : 20
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 27
% 0.19/0.37  # Removed in clause preprocessing      : 4
% 0.19/0.37  # Initial clauses in saturation        : 23
% 0.19/0.37  # Processed clauses                    : 60
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 10
% 0.19/0.37  # ...remaining for further processing  : 50
% 0.19/0.37  # Other redundant clauses eliminated   : 19
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 1
% 0.19/0.37  # Backward-rewritten                   : 6
% 0.19/0.37  # Generated clauses                    : 129
% 0.19/0.37  # ...of the previous two non-trivial   : 114
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 94
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 35
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 34
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 27
% 0.19/0.37  # Current number of unprocessed clauses: 73
% 0.19/0.37  # ...number of literals in the above   : 379
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 11
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 178
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 171
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 11
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3268
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
