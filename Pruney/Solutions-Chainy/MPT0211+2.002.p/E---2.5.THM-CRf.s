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
% DateTime   : Thu Dec  3 10:36:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 130 expanded)
%              Number of clauses        :   21 (  53 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 ( 130 expanded)
%              Number of equality atoms :   41 ( 129 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t100_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_11,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X125,X126] : k1_enumset1(X125,X125,X126) = k2_tarski(X125,X126) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X71,X72] : k2_tarski(X71,X72) = k2_xboole_0(k1_tarski(X71),k1_tarski(X72)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_14,plain,(
    ! [X124] : k2_tarski(X124,X124) = k1_tarski(X124) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X73,X74,X75] : k1_enumset1(X73,X74,X75) = k2_xboole_0(k1_tarski(X73),k2_tarski(X74,X75)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X61,X62,X63] : k1_enumset1(X61,X62,X63) = k1_enumset1(X62,X63,X61) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X79,X80,X81,X82] : k2_enumset1(X79,X80,X81,X82) = k2_xboole_0(k1_tarski(X79),k1_enumset1(X80,X81,X82)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk2_0,esk2_0,esk1_0),k1_enumset1(esk3_0,esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_20]),c_0_17]),c_0_17])).

fof(c_0_27,plain,(
    ! [X52,X53,X54,X55] : k2_enumset1(X52,X53,X54,X55) = k2_xboole_0(k2_tarski(X52,X53),k2_tarski(X54,X55)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk2_0),k1_enumset1(esk1_0,esk3_0,esk3_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X2,X2) = k1_enumset1(X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_17])).

fof(c_0_33,plain,(
    ! [X135,X136,X137] : k1_enumset1(X135,X136,X137) = k1_enumset1(X135,X137,X136) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

fof(c_0_34,plain,(
    ! [X40,X41] : k2_xboole_0(X40,k2_xboole_0(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk2_0),k1_enumset1(esk1_0,esk1_0,esk3_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_17]),c_0_17]),c_0_32])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_24]),c_0_37])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3)) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.028 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.21/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.45  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.45  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.21/0.45  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 0.21/0.45  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.21/0.45  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.21/0.45  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 0.21/0.45  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.21/0.45  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.21/0.45  fof(c_0_11, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.21/0.45  fof(c_0_12, plain, ![X125, X126]:k1_enumset1(X125,X125,X126)=k2_tarski(X125,X126), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.45  fof(c_0_13, plain, ![X71, X72]:k2_tarski(X71,X72)=k2_xboole_0(k1_tarski(X71),k1_tarski(X72)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.45  fof(c_0_14, plain, ![X124]:k2_tarski(X124,X124)=k1_tarski(X124), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.45  fof(c_0_15, plain, ![X73, X74, X75]:k1_enumset1(X73,X74,X75)=k2_xboole_0(k1_tarski(X73),k2_tarski(X74,X75)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.21/0.45  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.45  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.45  fof(c_0_18, plain, ![X61, X62, X63]:k1_enumset1(X61,X62,X63)=k1_enumset1(X62,X63,X61), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.21/0.45  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.45  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.45  cnf(c_0_21, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.45  fof(c_0_22, plain, ![X79, X80, X81, X82]:k2_enumset1(X79,X80,X81,X82)=k2_xboole_0(k1_tarski(X79),k1_enumset1(X80,X81,X82)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.21/0.45  cnf(c_0_23, negated_conjecture, (k2_xboole_0(k1_enumset1(esk2_0,esk2_0,esk1_0),k1_enumset1(esk3_0,esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.21/0.45  cnf(c_0_24, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20]), c_0_17]), c_0_17]), c_0_17])).
% 0.21/0.45  cnf(c_0_26, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_20]), c_0_17]), c_0_17])).
% 0.21/0.45  fof(c_0_27, plain, ![X52, X53, X54, X55]:k2_enumset1(X52,X53,X54,X55)=k2_xboole_0(k2_tarski(X52,X53),k2_tarski(X54,X55)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.21/0.45  cnf(c_0_28, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.45  cnf(c_0_29, negated_conjecture, (k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk2_0),k1_enumset1(esk1_0,esk3_0,esk3_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.21/0.45  cnf(c_0_30, plain, (k1_enumset1(X1,X2,X2)=k1_enumset1(X1,X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.45  cnf(c_0_31, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_32, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_17])).
% 0.21/0.45  fof(c_0_33, plain, ![X135, X136, X137]:k1_enumset1(X135,X136,X137)=k1_enumset1(X135,X137,X136), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.21/0.45  fof(c_0_34, plain, ![X40, X41]:k2_xboole_0(X40,k2_xboole_0(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.21/0.45  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk2_0),k1_enumset1(esk1_0,esk1_0,esk3_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30])).
% 0.21/0.45  cnf(c_0_36, plain, (k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))=k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_17]), c_0_17]), c_0_32])).
% 0.21/0.45  cnf(c_0_37, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.45  cnf(c_0_39, negated_conjecture, (k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_24]), c_0_37])).
% 0.21/0.45  cnf(c_0_40, plain, (k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3))=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_26])).
% 0.21/0.45  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 42
% 0.21/0.45  # Proof object clause steps            : 21
% 0.21/0.45  # Proof object formula steps           : 21
% 0.21/0.45  # Proof object conjectures             : 9
% 0.21/0.45  # Proof object clause conjectures      : 6
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 10
% 0.21/0.45  # Proof object initial formulas used   : 10
% 0.21/0.45  # Proof object generating inferences   : 1
% 0.21/0.45  # Proof object simplifying inferences  : 25
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 41
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 43
% 0.21/0.45  # Removed in clause preprocessing      : 6
% 0.21/0.45  # Initial clauses in saturation        : 37
% 0.21/0.45  # Processed clauses                    : 908
% 0.21/0.45  # ...of these trivial                  : 44
% 0.21/0.45  # ...subsumed                          : 657
% 0.21/0.45  # ...remaining for further processing  : 207
% 0.21/0.45  # Other redundant clauses eliminated   : 4
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 6
% 0.21/0.45  # Backward-rewritten                   : 11
% 0.21/0.45  # Generated clauses                    : 6982
% 0.21/0.45  # ...of the previous two non-trivial   : 5538
% 0.21/0.45  # Contextual simplify-reflections      : 0
% 0.21/0.45  # Paramodulations                      : 6976
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 6
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 156
% 0.21/0.45  #    Positive orientable unit clauses  : 49
% 0.21/0.45  #    Positive unorientable unit clauses: 15
% 0.21/0.45  #    Negative unit clauses             : 0
% 0.21/0.45  #    Non-unit-clauses                  : 92
% 0.21/0.45  # Current number of unprocessed clauses: 4667
% 0.21/0.45  # ...number of literals in the above   : 10397
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 54
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 3443
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 3254
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 441
% 0.21/0.45  # Unit Clause-clause subsumption calls : 139
% 0.21/0.45  # Rewrite failures with RHS unbound    : 28
% 0.21/0.45  # BW rewrite match attempts            : 542
% 0.21/0.45  # BW rewrite match successes           : 226
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 56958
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.105 s
% 0.21/0.46  # System time              : 0.007 s
% 0.21/0.46  # Total time               : 0.112 s
% 0.21/0.46  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
