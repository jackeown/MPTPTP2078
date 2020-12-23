%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  77 expanded)
%              Number of clauses        :   20 (  32 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 174 expanded)
%              Number of equality atoms :   90 ( 124 expanded)
%              Maximal formula depth    :   42 (   4 average)
%              Maximal clause size      :   60 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

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

fof(d5_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( X8 = k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X9 != X1
              & X9 != X2
              & X9 != X3
              & X9 != X4
              & X9 != X5
              & X9 != X6
              & X9 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(t10_ordinal1,conjecture,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_11,plain,(
    ! [X40,X41] : k3_tarski(k2_tarski(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X17)
        | r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_19,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k5_enumset1(X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59] :
      ( ( ~ r2_hidden(X50,X49)
        | X50 = X42
        | X50 = X43
        | X50 = X44
        | X50 = X45
        | X50 = X46
        | X50 = X47
        | X50 = X48
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X42
        | r2_hidden(X51,X49)
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X43
        | r2_hidden(X51,X49)
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X44
        | r2_hidden(X51,X49)
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X45
        | r2_hidden(X51,X49)
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X46
        | r2_hidden(X51,X49)
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X47
        | r2_hidden(X51,X49)
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X48
        | r2_hidden(X51,X49)
        | X49 != k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) != X52
        | ~ r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) != X53
        | ~ r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) != X54
        | ~ r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) != X55
        | ~ r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) != X56
        | ~ r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) != X57
        | ~ r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) != X58
        | ~ r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) = X52
        | esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) = X53
        | esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) = X54
        | esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) = X55
        | esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) = X56
        | esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) = X57
        | esk2_8(X52,X53,X54,X55,X56,X57,X58,X59) = X58
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(assume_negation,[status(cth)],[t10_ordinal1])).

fof(c_0_22,plain,(
    ! [X61] : k1_ordinal1(X61) = k2_xboole_0(X61,k1_tarski(X61)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_23,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X5,X6,X7,X8,X9,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,negated_conjecture,(
    ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_32,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X4,X5,X6,X7,X8,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_15]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X3,X4,X5,X6,X7,X8,X1)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.40  # and selection function SelectNegativeLiterals.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.040 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.40  fof(d5_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(X8=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)<=>![X9]:(r2_hidden(X9,X8)<=>~(((((((X9!=X1&X9!=X2)&X9!=X3)&X9!=X4)&X9!=X5)&X9!=X6)&X9!=X7)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 0.20/0.40  fof(t10_ordinal1, conjecture, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.20/0.40  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(c_0_11, plain, ![X40, X41]:k3_tarski(k2_tarski(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.40  fof(c_0_12, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_13, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X13,X12)|(r2_hidden(X13,X10)|r2_hidden(X13,X11))|X12!=k2_xboole_0(X10,X11))&((~r2_hidden(X14,X10)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))&(~r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))))&(((~r2_hidden(esk1_3(X15,X16,X17),X15)|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16))&(~r2_hidden(esk1_3(X15,X16,X17),X16)|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16)))&(r2_hidden(esk1_3(X15,X16,X17),X17)|(r2_hidden(esk1_3(X15,X16,X17),X15)|r2_hidden(esk1_3(X15,X16,X17),X16))|X17=k2_xboole_0(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  fof(c_0_16, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_17, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  fof(c_0_18, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.40  fof(c_0_19, plain, ![X34, X35, X36, X37, X38, X39]:k5_enumset1(X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.40  fof(c_0_20, plain, ![X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59]:(((~r2_hidden(X50,X49)|(X50=X42|X50=X43|X50=X44|X50=X45|X50=X46|X50=X47|X50=X48)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48))&(((((((X51!=X42|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48))&(X51!=X43|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X44|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X45|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X46|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X47|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X48|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48))))&((((((((esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X52|~r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58))&(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X53|~r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X54|~r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X55|~r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X56|~r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X57|~r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X58|~r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(r2_hidden(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|(esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)=X52|esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)=X53|esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)=X54|esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)=X55|esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)=X56|esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)=X57|esk2_8(X52,X53,X54,X55,X56,X57,X58,X59)=X58)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).
% 0.20/0.40  fof(c_0_21, negated_conjecture, ~(![X1]:r2_hidden(X1,k1_ordinal1(X1))), inference(assume_negation,[status(cth)],[t10_ordinal1])).
% 0.20/0.40  fof(c_0_22, plain, ![X61]:k1_ordinal1(X61)=k2_xboole_0(X61,k1_tarski(X61)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.20/0.40  fof(c_0_23, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_25, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.40  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X5,X6,X7,X8,X9,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  fof(c_0_31, negated_conjecture, ~r2_hidden(esk3_0,k1_ordinal1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.40  cnf(c_0_32, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.40  cnf(c_0_35, plain, (r2_hidden(X1,X2)|X2!=k5_enumset1(X3,X4,X5,X6,X7,X8,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk3_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_37, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.40  cnf(c_0_38, plain, (r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_39, plain, (r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1))), inference(er,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk3_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_15]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.40  cnf(c_0_41, plain, (r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X3,X4,X5,X6,X7,X8,X1))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 43
% 0.20/0.40  # Proof object clause steps            : 20
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 6
% 0.20/0.40  # Proof object clause conjectures      : 3
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 11
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 3
% 0.20/0.40  # Proof object simplifying inferences  : 21
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 31
% 0.20/0.40  # Removed in clause preprocessing      : 8
% 0.20/0.40  # Initial clauses in saturation        : 23
% 0.20/0.40  # Processed clauses                    : 51
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 0
% 0.20/0.40  # ...remaining for further processing  : 51
% 0.20/0.40  # Other redundant clauses eliminated   : 11
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 1
% 0.20/0.40  # Generated clauses                    : 203
% 0.20/0.40  # ...of the previous two non-trivial   : 173
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 176
% 0.20/0.40  # Factorizations                       : 4
% 0.20/0.40  # Equation resolutions                 : 23
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 43
% 0.20/0.40  #    Positive orientable unit clauses  : 8
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 0
% 0.20/0.40  #    Non-unit-clauses                  : 35
% 0.20/0.40  # Current number of unprocessed clauses: 145
% 0.20/0.40  # ...number of literals in the above   : 899
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 9
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 749
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 262
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 64
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 37
% 0.20/0.40  # BW rewrite match successes           : 1
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 8663
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.047 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.053 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
