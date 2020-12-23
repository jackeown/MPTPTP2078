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
% DateTime   : Thu Dec  3 10:37:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 161 expanded)
%              Number of clauses        :   26 (  63 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 244 expanded)
%              Number of equality atoms :   81 ( 218 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X30,X31] : k2_xboole_0(X30,X31) = k5_xboole_0(k5_xboole_0(X30,X31),k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_13,plain,(
    ! [X32,X33] : k2_xboole_0(X32,X33) = k5_xboole_0(X32,k4_xboole_0(X33,X32)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_14,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X56] : k2_tarski(X56,X56) = k1_tarski(X56) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X57,X58] : k1_enumset1(X57,X57,X58) = k2_tarski(X57,X58) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X59,X60,X61] : k2_enumset1(X59,X59,X60,X61) = k1_enumset1(X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X62,X63,X64,X65] : k3_enumset1(X62,X62,X63,X64,X65) = k2_enumset1(X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X27,X28,X29] : k5_xboole_0(k5_xboole_0(X27,X28),X29) = k5_xboole_0(X27,k5_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_24,plain,(
    ! [X52,X53,X54,X55] : k2_enumset1(X52,X53,X54,X55) = k2_xboole_0(k2_tarski(X52,X53),k2_tarski(X54,X55)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_25,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X38,X37)
        | X38 = X34
        | X38 = X35
        | X38 = X36
        | X37 != k1_enumset1(X34,X35,X36) )
      & ( X39 != X34
        | r2_hidden(X39,X37)
        | X37 != k1_enumset1(X34,X35,X36) )
      & ( X39 != X35
        | r2_hidden(X39,X37)
        | X37 != k1_enumset1(X34,X35,X36) )
      & ( X39 != X36
        | r2_hidden(X39,X37)
        | X37 != k1_enumset1(X34,X35,X36) )
      & ( esk2_4(X40,X41,X42,X43) != X40
        | ~ r2_hidden(esk2_4(X40,X41,X42,X43),X43)
        | X43 = k1_enumset1(X40,X41,X42) )
      & ( esk2_4(X40,X41,X42,X43) != X41
        | ~ r2_hidden(esk2_4(X40,X41,X42,X43),X43)
        | X43 = k1_enumset1(X40,X41,X42) )
      & ( esk2_4(X40,X41,X42,X43) != X42
        | ~ r2_hidden(esk2_4(X40,X41,X42,X43),X43)
        | X43 = k1_enumset1(X40,X41,X42) )
      & ( r2_hidden(esk2_4(X40,X41,X42,X43),X43)
        | esk2_4(X40,X41,X42,X43) = X40
        | esk2_4(X40,X41,X42,X43) = X41
        | esk2_4(X40,X41,X42,X43) = X42
        | X43 = k1_enumset1(X40,X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_21]),c_0_22]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_28]),c_0_28]),c_0_21]),c_0_22]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_38,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_29]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)))) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_42,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_29]),c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk5_0,esk5_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:40:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.54  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.54  # and selection function SelectNegativeLiterals.
% 0.19/0.54  #
% 0.19/0.54  # Preprocessing time       : 0.029 s
% 0.19/0.54  # Presaturation interreduction done
% 0.19/0.54  
% 0.19/0.54  # Proof found!
% 0.19/0.54  # SZS status Theorem
% 0.19/0.54  # SZS output start CNFRefutation
% 0.19/0.54  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.19/0.54  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.19/0.54  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.54  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.54  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.54  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.54  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.54  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.54  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.54  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.19/0.54  fof(c_0_12, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(k5_xboole_0(X30,X31),k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.19/0.54  fof(c_0_13, plain, ![X32, X33]:k2_xboole_0(X32,X33)=k5_xboole_0(X32,k4_xboole_0(X33,X32)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.54  fof(c_0_14, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.54  fof(c_0_15, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)&esk4_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.54  fof(c_0_16, plain, ![X56]:k2_tarski(X56,X56)=k1_tarski(X56), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.54  fof(c_0_17, plain, ![X57, X58]:k1_enumset1(X57,X57,X58)=k2_tarski(X57,X58), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.54  fof(c_0_18, plain, ![X59, X60, X61]:k2_enumset1(X59,X59,X60,X61)=k1_enumset1(X59,X60,X61), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.54  fof(c_0_19, plain, ![X62, X63, X64, X65]:k3_enumset1(X62,X62,X63,X64,X65)=k2_enumset1(X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.54  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.54  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.54  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.54  fof(c_0_23, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.54  fof(c_0_24, plain, ![X52, X53, X54, X55]:k2_enumset1(X52,X53,X54,X55)=k2_xboole_0(k2_tarski(X52,X53),k2_tarski(X54,X55)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.54  fof(c_0_25, plain, ![X34, X35, X36, X37, X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X38,X37)|(X38=X34|X38=X35|X38=X36)|X37!=k1_enumset1(X34,X35,X36))&(((X39!=X34|r2_hidden(X39,X37)|X37!=k1_enumset1(X34,X35,X36))&(X39!=X35|r2_hidden(X39,X37)|X37!=k1_enumset1(X34,X35,X36)))&(X39!=X36|r2_hidden(X39,X37)|X37!=k1_enumset1(X34,X35,X36))))&((((esk2_4(X40,X41,X42,X43)!=X40|~r2_hidden(esk2_4(X40,X41,X42,X43),X43)|X43=k1_enumset1(X40,X41,X42))&(esk2_4(X40,X41,X42,X43)!=X41|~r2_hidden(esk2_4(X40,X41,X42,X43),X43)|X43=k1_enumset1(X40,X41,X42)))&(esk2_4(X40,X41,X42,X43)!=X42|~r2_hidden(esk2_4(X40,X41,X42,X43),X43)|X43=k1_enumset1(X40,X41,X42)))&(r2_hidden(esk2_4(X40,X41,X42,X43),X43)|(esk2_4(X40,X41,X42,X43)=X40|esk2_4(X40,X41,X42,X43)=X41|esk2_4(X40,X41,X42,X43)=X42)|X43=k1_enumset1(X40,X41,X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.54  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.54  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.54  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.54  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.54  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.19/0.54  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.54  cnf(c_0_33, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.54  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.54  cnf(c_0_35, negated_conjecture, (k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_21]), c_0_22]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.19/0.54  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.54  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_28]), c_0_28]), c_0_21]), c_0_22]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.19/0.54  cnf(c_0_38, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.54  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_29]), c_0_30])).
% 0.19/0.54  cnf(c_0_40, negated_conjecture, (k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.54  cnf(c_0_41, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))))=k3_enumset1(X1,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.19/0.54  cnf(c_0_42, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_29]), c_0_30])).
% 0.19/0.54  cnf(c_0_43, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.19/0.54  cnf(c_0_44, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk5_0,esk5_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.54  cnf(c_0_45, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_42])).
% 0.19/0.54  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.54  cnf(c_0_47, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.54  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), ['proof']).
% 0.19/0.54  # SZS output end CNFRefutation
% 0.19/0.54  # Proof object total steps             : 49
% 0.19/0.54  # Proof object clause steps            : 26
% 0.19/0.54  # Proof object formula steps           : 23
% 0.19/0.54  # Proof object conjectures             : 10
% 0.19/0.54  # Proof object clause conjectures      : 7
% 0.19/0.54  # Proof object formula conjectures     : 3
% 0.19/0.54  # Proof object initial clauses used    : 13
% 0.19/0.54  # Proof object initial formulas used   : 11
% 0.19/0.54  # Proof object generating inferences   : 3
% 0.19/0.54  # Proof object simplifying inferences  : 44
% 0.19/0.54  # Training examples: 0 positive, 0 negative
% 0.19/0.54  # Parsed axioms                        : 20
% 0.19/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.54  # Initial clauses                      : 38
% 0.19/0.54  # Removed in clause preprocessing      : 6
% 0.19/0.54  # Initial clauses in saturation        : 32
% 0.19/0.54  # Processed clauses                    : 981
% 0.19/0.54  # ...of these trivial                  : 43
% 0.19/0.54  # ...subsumed                          : 660
% 0.19/0.54  # ...remaining for further processing  : 278
% 0.19/0.54  # Other redundant clauses eliminated   : 32
% 0.19/0.54  # Clauses deleted for lack of memory   : 0
% 0.19/0.54  # Backward-subsumed                    : 1
% 0.19/0.54  # Backward-rewritten                   : 13
% 0.19/0.54  # Generated clauses                    : 11402
% 0.19/0.54  # ...of the previous two non-trivial   : 9230
% 0.19/0.54  # Contextual simplify-reflections      : 0
% 0.19/0.54  # Paramodulations                      : 11368
% 0.19/0.54  # Factorizations                       : 6
% 0.19/0.54  # Equation resolutions                 : 32
% 0.19/0.54  # Propositional unsat checks           : 0
% 0.19/0.54  #    Propositional check models        : 0
% 0.19/0.54  #    Propositional check unsatisfiable : 0
% 0.19/0.54  #    Propositional clauses             : 0
% 0.19/0.54  #    Propositional clauses after purity: 0
% 0.19/0.54  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 226
% 0.19/0.54  #    Positive orientable unit clauses  : 118
% 0.19/0.54  #    Positive unorientable unit clauses: 3
% 0.19/0.54  #    Negative unit clauses             : 21
% 0.19/0.54  #    Non-unit-clauses                  : 84
% 0.19/0.54  # Current number of unprocessed clauses: 8279
% 0.19/0.54  # ...number of literals in the above   : 20987
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 50
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 4722
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 3082
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 242
% 0.19/0.54  # Unit Clause-clause subsumption calls : 320
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 1076
% 0.19/0.54  # BW rewrite match successes           : 37
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 364958
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.194 s
% 0.19/0.54  # System time              : 0.009 s
% 0.19/0.54  # Total time               : 0.203 s
% 0.19/0.54  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
