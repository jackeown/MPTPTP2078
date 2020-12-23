%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:08 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  77 expanded)
%              Number of clauses        :   24 (  32 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  132 ( 225 expanded)
%              Number of equality atoms :   94 ( 170 expanded)
%              Maximal formula depth    :   42 (   4 average)
%              Maximal clause size      :   60 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t14_ordinal1,conjecture,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_13,plain,(
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
      & ( esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) != X52
        | ~ r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) != X53
        | ~ r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) != X54
        | ~ r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) != X55
        | ~ r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) != X56
        | ~ r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) != X57
        | ~ r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) != X58
        | ~ r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) )
      & ( r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) = X52
        | esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) = X53
        | esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) = X54
        | esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) = X55
        | esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) = X56
        | esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) = X57
        | esk1_8(X52,X53,X54,X55,X56,X57,X58,X59) = X58
        | X59 = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).

fof(c_0_14,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37) = k5_enumset1(X31,X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X5,X6,X7,X8,X9,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] : X1 != k1_ordinal1(X1) ),
    inference(assume_negation,[status(cth)],[t14_ordinal1])).

fof(c_0_18,plain,(
    ! [X61] : k1_ordinal1(X61) = k2_xboole_0(X61,k1_tarski(X61)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_19,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X40,X41] : k3_tarski(k2_tarski(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X38,X39] :
      ( ~ r2_hidden(X38,X39)
      | r1_tarski(X38,k3_tarski(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X5,X6,X7,X8,X9,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_24,negated_conjecture,(
    esk2_0 = k1_ordinal1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_25,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X16,X17,X18,X19] : k3_enumset1(X16,X16,X17,X18,X19) = k2_enumset1(X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X20,X21,X22,X23,X24] : k4_enumset1(X20,X20,X21,X22,X23,X24) = k3_enumset1(X20,X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X25,X26,X27,X28,X29,X30] : k5_enumset1(X25,X25,X26,X27,X28,X29,X30) = k4_enumset1(X25,X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = k1_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X4,X5,X6,X7,X8,X9) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_43,plain,(
    ! [X62,X63] :
      ( ~ r2_hidden(X62,X63)
      | ~ r1_tarski(X63,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 = k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_28]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_16]),c_0_16])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_42,c_0_16])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.13/0.39  # and selection function GSelectMinInfpos.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.043 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d5_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(X8=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)<=>![X9]:(r2_hidden(X9,X8)<=>~(((((((X9!=X1&X9!=X2)&X9!=X3)&X9!=X4)&X9!=X5)&X9!=X6)&X9!=X7)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 0.13/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.39  fof(t14_ordinal1, conjecture, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.13/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.39  fof(c_0_13, plain, ![X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59]:(((~r2_hidden(X50,X49)|(X50=X42|X50=X43|X50=X44|X50=X45|X50=X46|X50=X47|X50=X48)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48))&(((((((X51!=X42|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48))&(X51!=X43|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X44|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X45|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X46|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X47|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(X51!=X48|r2_hidden(X51,X49)|X49!=k5_enumset1(X42,X43,X44,X45,X46,X47,X48))))&((((((((esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X52|~r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58))&(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X53|~r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X54|~r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X55|~r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X56|~r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X57|~r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)!=X58|~r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))&(r2_hidden(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59),X59)|(esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)=X52|esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)=X53|esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)=X54|esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)=X55|esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)=X56|esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)=X57|esk1_8(X52,X53,X54,X55,X56,X57,X58,X59)=X58)|X59=k5_enumset1(X52,X53,X54,X55,X56,X57,X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).
% 0.13/0.39  fof(c_0_14, plain, ![X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37)=k5_enumset1(X31,X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.39  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X5,X6,X7,X8,X9,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_16, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:X1!=k1_ordinal1(X1)), inference(assume_negation,[status(cth)],[t14_ordinal1])).
% 0.13/0.39  fof(c_0_18, plain, ![X61]:k1_ordinal1(X61)=k2_xboole_0(X61,k1_tarski(X61)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.39  fof(c_0_19, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_20, plain, ![X40, X41]:k3_tarski(k2_tarski(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.39  fof(c_0_21, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X38, X39]:(~r2_hidden(X38,X39)|r1_tarski(X38,k3_tarski(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.13/0.39  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X5,X6,X7,X8,X9,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  fof(c_0_24, negated_conjecture, esk2_0=k1_ordinal1(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.39  cnf(c_0_25, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  fof(c_0_29, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_30, plain, ![X16, X17, X18, X19]:k3_enumset1(X16,X16,X17,X18,X19)=k2_enumset1(X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_31, plain, ![X20, X21, X22, X23, X24]:k4_enumset1(X20,X20,X21,X22,X23,X24)=k3_enumset1(X20,X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.39  fof(c_0_32, plain, ![X25, X26, X27, X28, X29, X30]:k5_enumset1(X25,X25,X26,X27,X28,X29,X30)=k4_enumset1(X25,X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.39  cnf(c_0_33, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_34, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (esk2_0=k1_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_36, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.39  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.39  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X4,X5,X6,X7,X8,X9)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_43, plain, ![X62, X63]:(~r2_hidden(X62,X63)|~r1_tarski(X63,X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.39  cnf(c_0_44, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X1)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (esk2_0=k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_28]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_16]), c_0_16])).
% 0.13/0.39  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_42, c_0_16])).
% 0.13/0.39  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.39  cnf(c_0_49, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 51
% 0.13/0.39  # Proof object clause steps            : 24
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 7
% 0.13/0.39  # Proof object clause conjectures      : 4
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 14
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 3
% 0.13/0.39  # Proof object simplifying inferences  : 23
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 28
% 0.13/0.39  # Removed in clause preprocessing      : 9
% 0.13/0.39  # Initial clauses in saturation        : 19
% 0.13/0.39  # Processed clauses                    : 40
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 40
% 0.13/0.39  # Other redundant clauses eliminated   : 15
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 0
% 0.13/0.39  # Generated clauses                    : 18
% 0.13/0.39  # ...of the previous two non-trivial   : 17
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 10
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 15
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
% 0.13/0.39  # Current number of processed clauses  : 13
% 0.13/0.39  #    Positive orientable unit clauses  : 10
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 3
% 0.13/0.39  # Current number of unprocessed clauses: 15
% 0.13/0.39  # ...number of literals in the above   : 37
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 28
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 43
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 43
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 42
% 0.13/0.39  # BW rewrite match successes           : 0
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1620
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.047 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
