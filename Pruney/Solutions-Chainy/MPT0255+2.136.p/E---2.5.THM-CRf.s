%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:37 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 180 expanded)
%              Number of clauses        :   27 (  75 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 212 expanded)
%              Number of equality atoms :   62 ( 188 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t65_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(t95_enumset1,axiom,(
    ! [X1,X2] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).

fof(t105_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & k4_xboole_0(X2,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k2_xboole_0(X13,X14)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_15,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X28,X29] : k2_enumset1(X28,X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_17,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r1_tarski(X39,k2_tarski(X40,X41))
        | X39 = k1_xboole_0
        | X39 = k1_tarski(X40)
        | X39 = k1_tarski(X41)
        | X39 = k2_tarski(X40,X41) )
      & ( X39 != k1_xboole_0
        | r1_tarski(X39,k2_tarski(X40,X41)) )
      & ( X39 != k1_tarski(X40)
        | r1_tarski(X39,k2_tarski(X40,X41)) )
      & ( X39 != k1_tarski(X41)
        | r1_tarski(X39,k2_tarski(X40,X41)) )
      & ( X39 != k2_tarski(X40,X41)
        | r1_tarski(X39,k2_tarski(X40,X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_19,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] : k6_enumset1(X15,X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k2_enumset1(X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t65_enumset1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X44,X45] : k2_xboole_0(k1_tarski(X44),X45) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X36] : k3_enumset1(X36,X36,X36,X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_27,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k6_enumset1(X30,X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X37,X38] : k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t95_enumset1])).

fof(c_0_31,plain,(
    ! [X11,X12] :
      ( ~ r2_xboole_0(X11,X12)
      | k4_xboole_0(X12,X11) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_21]),c_0_22]),c_0_22])).

fof(c_0_34,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | ~ r2_xboole_0(X9,X10) )
      & ( X9 != X10
        | ~ r2_xboole_0(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | X9 = X10
        | r2_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k2_enumset1(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_21]),c_0_22])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( ~ r2_xboole_0(X1,X2)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k3_tarski(k2_enumset1(k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_21]),c_0_22]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_47,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_22]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_xboole_0(k1_xboole_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_51,c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:01:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.14/0.37  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.14/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.14/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.14/0.37  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.14/0.37  fof(t65_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_enumset1)).
% 0.14/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.14/0.37  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 0.14/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.37  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.14/0.37  fof(t95_enumset1, axiom, ![X1, X2]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_enumset1)).
% 0.14/0.37  fof(t105_xboole_1, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&k4_xboole_0(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 0.14/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.14/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.14/0.37  fof(c_0_14, plain, ![X13, X14]:k4_xboole_0(X13,k2_xboole_0(X13,X14))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.14/0.37  fof(c_0_15, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.14/0.37  fof(c_0_16, plain, ![X28, X29]:k2_enumset1(X28,X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.14/0.37  fof(c_0_17, negated_conjecture, k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.37  fof(c_0_18, plain, ![X39, X40, X41]:((~r1_tarski(X39,k2_tarski(X40,X41))|(X39=k1_xboole_0|X39=k1_tarski(X40)|X39=k1_tarski(X41)|X39=k2_tarski(X40,X41)))&((((X39!=k1_xboole_0|r1_tarski(X39,k2_tarski(X40,X41)))&(X39!=k1_tarski(X40)|r1_tarski(X39,k2_tarski(X40,X41))))&(X39!=k1_tarski(X41)|r1_tarski(X39,k2_tarski(X40,X41))))&(X39!=k2_tarski(X40,X41)|r1_tarski(X39,k2_tarski(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.14/0.37  fof(c_0_19, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:k6_enumset1(X15,X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k2_enumset1(X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[t65_enumset1])).
% 0.14/0.37  cnf(c_0_20, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_24, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  fof(c_0_25, plain, ![X44, X45]:k2_xboole_0(k1_tarski(X44),X45)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.14/0.37  fof(c_0_26, plain, ![X36]:k3_enumset1(X36,X36,X36,X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.14/0.37  fof(c_0_27, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.37  fof(c_0_28, plain, ![X30, X31, X32, X33, X34, X35]:k6_enumset1(X30,X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.14/0.37  cnf(c_0_29, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.37  fof(c_0_30, plain, ![X37, X38]:k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t95_enumset1])).
% 0.14/0.37  fof(c_0_31, plain, ![X11, X12]:(~r2_xboole_0(X11,X12)|k4_xboole_0(X12,X11)!=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).
% 0.14/0.37  cnf(c_0_32, plain, (k4_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_21]), c_0_22]), c_0_22])).
% 0.14/0.37  fof(c_0_34, plain, ![X9, X10]:(((r1_tarski(X9,X10)|~r2_xboole_0(X9,X10))&(X9!=X10|~r2_xboole_0(X9,X10)))&(~r1_tarski(X9,X10)|X9=X10|r2_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.14/0.37  cnf(c_0_35, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 0.14/0.37  cnf(c_0_36, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.37  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.37  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.37  cnf(c_0_40, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k2_enumset1(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_21]), c_0_22])).
% 0.14/0.37  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.37  cnf(c_0_42, plain, (~r2_xboole_0(X1,X2)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.37  cnf(c_0_44, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.37  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.14/0.37  cnf(c_0_46, plain, (k3_tarski(k2_enumset1(k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_21]), c_0_22]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40])).
% 0.14/0.37  cnf(c_0_47, plain, (k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)))=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_22]), c_0_40])).
% 0.14/0.37  cnf(c_0_48, negated_conjecture, (~r2_xboole_0(k1_xboole_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.37  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|r2_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.37  cnf(c_0_50, plain, (k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_47])).
% 0.14/0.37  cnf(c_0_51, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.37  cnf(c_0_52, plain, (k2_enumset1(X1,X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_47])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_51, c_0_52]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 54
% 0.14/0.37  # Proof object clause steps            : 27
% 0.14/0.37  # Proof object formula steps           : 27
% 0.14/0.37  # Proof object conjectures             : 9
% 0.14/0.37  # Proof object clause conjectures      : 6
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 13
% 0.14/0.37  # Proof object initial formulas used   : 13
% 0.14/0.37  # Proof object generating inferences   : 5
% 0.14/0.37  # Proof object simplifying inferences  : 29
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 13
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 19
% 0.14/0.37  # Removed in clause preprocessing      : 6
% 0.14/0.37  # Initial clauses in saturation        : 13
% 0.14/0.37  # Processed clauses                    : 65
% 0.14/0.37  # ...of these trivial                  : 2
% 0.14/0.37  # ...subsumed                          : 13
% 0.14/0.37  # ...remaining for further processing  : 50
% 0.14/0.37  # Other redundant clauses eliminated   : 5
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 4
% 0.14/0.37  # Generated clauses                    : 62
% 0.14/0.37  # ...of the previous two non-trivial   : 48
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 53
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 5
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 24
% 0.14/0.37  #    Positive orientable unit clauses  : 14
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 7
% 0.14/0.37  #    Non-unit-clauses                  : 3
% 0.14/0.37  # Current number of unprocessed clauses: 7
% 0.14/0.37  # ...number of literals in the above   : 13
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 27
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 1
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 2
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 13
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1601
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.028 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.033 s
% 0.14/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
