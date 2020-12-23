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
% DateTime   : Thu Dec  3 10:43:10 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 136 expanded)
%              Number of clauses        :   29 (  57 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 229 expanded)
%              Number of equality atoms :   56 ( 154 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t81_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X13
        | X17 = X14
        | X17 = X15
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X13
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X19,X20,X21,X22) != X19
        | ~ r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk1_4(X19,X20,X21,X22) != X20
        | ~ r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk1_4(X19,X20,X21,X22) != X21
        | ~ r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | esk1_4(X19,X20,X21,X22) = X19
        | esk1_4(X19,X20,X21,X22) = X20
        | esk1_4(X19,X20,X21,X22) = X21
        | X22 = k1_enumset1(X19,X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_13,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_16,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k5_enumset1(X38,X38,X39,X40,X41,X42,X43) = k4_enumset1(X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_17,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50) = k5_enumset1(X44,X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X53,X54] : k3_tarski(k2_tarski(X53,X54)) = k2_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | r1_tarski(X51,k3_tarski(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

fof(c_0_31,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X12,X11)
      | r1_tarski(k2_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X55,X56] :
      ( ~ r1_tarski(X55,X56)
      | r1_tarski(k1_zfmisc_1(X55),k1_zfmisc_1(X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_30])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t81_zfmisc_1])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_44,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk3_0)),k1_zfmisc_1(k2_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk3_0)),k1_zfmisc_1(k2_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))))
    | ~ r1_tarski(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk3_0))),k1_zfmisc_1(k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_40]),c_0_40]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 6.06/6.28  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 6.06/6.28  # and selection function SelectNegativeLiterals.
% 6.06/6.28  #
% 6.06/6.28  # Preprocessing time       : 0.027 s
% 6.06/6.28  
% 6.06/6.28  # Proof found!
% 6.06/6.28  # SZS status Theorem
% 6.06/6.28  # SZS output start CNFRefutation
% 6.06/6.28  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.06/6.28  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.06/6.28  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.06/6.28  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.06/6.28  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 6.06/6.28  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 6.06/6.28  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.06/6.28  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.06/6.28  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.06/6.28  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.06/6.28  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 6.06/6.28  fof(t81_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 6.06/6.28  fof(c_0_12, plain, ![X13, X14, X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X17,X16)|(X17=X13|X17=X14|X17=X15)|X16!=k1_enumset1(X13,X14,X15))&(((X18!=X13|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))&(X18!=X14|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15)))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))))&((((esk1_4(X19,X20,X21,X22)!=X19|~r2_hidden(esk1_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21))&(esk1_4(X19,X20,X21,X22)!=X20|~r2_hidden(esk1_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(esk1_4(X19,X20,X21,X22)!=X21|~r2_hidden(esk1_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(r2_hidden(esk1_4(X19,X20,X21,X22),X22)|(esk1_4(X19,X20,X21,X22)=X19|esk1_4(X19,X20,X21,X22)=X20|esk1_4(X19,X20,X21,X22)=X21)|X22=k1_enumset1(X19,X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 6.06/6.28  fof(c_0_13, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 6.06/6.28  fof(c_0_14, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 6.06/6.28  fof(c_0_15, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 6.06/6.28  fof(c_0_16, plain, ![X38, X39, X40, X41, X42, X43]:k5_enumset1(X38,X38,X39,X40,X41,X42,X43)=k4_enumset1(X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 6.06/6.28  fof(c_0_17, plain, ![X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50)=k5_enumset1(X44,X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 6.06/6.28  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 6.06/6.28  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.06/6.28  cnf(c_0_20, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.06/6.28  cnf(c_0_21, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.06/6.28  cnf(c_0_22, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.06/6.28  cnf(c_0_23, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.06/6.28  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 6.06/6.28  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 6.06/6.28  fof(c_0_26, plain, ![X53, X54]:k3_tarski(k2_tarski(X53,X54))=k2_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 6.06/6.28  fof(c_0_27, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.06/6.28  fof(c_0_28, plain, ![X51, X52]:(~r2_hidden(X51,X52)|r1_tarski(X51,k3_tarski(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 6.06/6.28  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_24])).
% 6.06/6.28  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 6.06/6.28  fof(c_0_31, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X12,X11)|r1_tarski(k2_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 6.06/6.28  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.06/6.28  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.06/6.28  fof(c_0_34, plain, ![X55, X56]:(~r1_tarski(X55,X56)|r1_tarski(k1_zfmisc_1(X55),k1_zfmisc_1(X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 6.06/6.28  cnf(c_0_35, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.06/6.28  cnf(c_0_36, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_29])).
% 6.06/6.28  cnf(c_0_37, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_30])).
% 6.06/6.28  fof(c_0_38, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t81_zfmisc_1])).
% 6.06/6.28  cnf(c_0_39, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 6.06/6.28  cnf(c_0_40, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 6.06/6.28  cnf(c_0_41, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 6.06/6.28  cnf(c_0_42, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 6.06/6.28  cnf(c_0_43, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_37])).
% 6.06/6.28  fof(c_0_44, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk3_0)),k1_zfmisc_1(k2_xboole_0(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 6.06/6.28  cnf(c_0_45, plain, (r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 6.06/6.28  cnf(c_0_46, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 6.06/6.28  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_43])).
% 6.06/6.28  cnf(c_0_48, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk3_0)),k1_zfmisc_1(k2_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 6.06/6.28  cnf(c_0_49, plain, (r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))))|~r1_tarski(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 6.06/6.28  cnf(c_0_50, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))))), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 6.06/6.28  cnf(c_0_51, negated_conjecture, (~r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk3_0))),k1_zfmisc_1(k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_40]), c_0_40]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 6.06/6.28  cnf(c_0_52, plain, (r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X2))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 6.06/6.28  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])]), ['proof']).
% 6.06/6.28  # SZS output end CNFRefutation
% 6.06/6.28  # Proof object total steps             : 54
% 6.06/6.28  # Proof object clause steps            : 29
% 6.06/6.28  # Proof object formula steps           : 25
% 6.06/6.28  # Proof object conjectures             : 6
% 6.06/6.28  # Proof object clause conjectures      : 3
% 6.06/6.28  # Proof object formula conjectures     : 3
% 6.06/6.28  # Proof object initial clauses used    : 13
% 6.06/6.28  # Proof object initial formulas used   : 12
% 6.06/6.28  # Proof object generating inferences   : 8
% 6.06/6.28  # Proof object simplifying inferences  : 33
% 6.06/6.28  # Training examples: 0 positive, 0 negative
% 6.06/6.28  # Parsed axioms                        : 13
% 6.06/6.28  # Removed by relevancy pruning/SinE    : 0
% 6.06/6.28  # Initial clauses                      : 20
% 6.06/6.28  # Removed in clause preprocessing      : 7
% 6.06/6.28  # Initial clauses in saturation        : 13
% 6.06/6.28  # Processed clauses                    : 1173
% 6.06/6.28  # ...of these trivial                  : 7
% 6.06/6.28  # ...subsumed                          : 224
% 6.06/6.28  # ...remaining for further processing  : 942
% 6.06/6.28  # Other redundant clauses eliminated   : 220
% 6.06/6.28  # Clauses deleted for lack of memory   : 0
% 6.06/6.28  # Backward-subsumed                    : 112
% 6.06/6.28  # Backward-rewritten                   : 11
% 6.06/6.28  # Generated clauses                    : 137767
% 6.06/6.28  # ...of the previous two non-trivial   : 136844
% 6.06/6.28  # Contextual simplify-reflections      : 1
% 6.06/6.28  # Paramodulations                      : 137497
% 6.06/6.28  # Factorizations                       : 30
% 6.06/6.28  # Equation resolutions                 : 240
% 6.06/6.28  # Propositional unsat checks           : 0
% 6.06/6.28  #    Propositional check models        : 0
% 6.06/6.28  #    Propositional check unsatisfiable : 0
% 6.06/6.28  #    Propositional clauses             : 0
% 6.06/6.28  #    Propositional clauses after purity: 0
% 6.06/6.28  #    Propositional unsat core size     : 0
% 6.06/6.28  #    Propositional preprocessing time  : 0.000
% 6.06/6.28  #    Propositional encoding time       : 0.000
% 6.06/6.28  #    Propositional solver time         : 0.000
% 6.06/6.28  #    Success case prop preproc time    : 0.000
% 6.06/6.28  #    Success case prop encoding time   : 0.000
% 6.06/6.28  #    Success case prop solver time     : 0.000
% 6.06/6.28  # Current number of processed clauses  : 816
% 6.06/6.28  #    Positive orientable unit clauses  : 173
% 6.06/6.28  #    Positive unorientable unit clauses: 0
% 6.06/6.28  #    Negative unit clauses             : 0
% 6.06/6.28  #    Non-unit-clauses                  : 643
% 6.06/6.28  # Current number of unprocessed clauses: 135254
% 6.06/6.28  # ...number of literals in the above   : 1343421
% 6.06/6.28  # Current number of archived formulas  : 0
% 6.06/6.28  # Current number of archived clauses   : 130
% 6.06/6.28  # Clause-clause subsumption calls (NU) : 104884
% 6.06/6.28  # Rec. Clause-clause subsumption calls : 9740
% 6.06/6.28  # Non-unit clause-clause subsumptions  : 337
% 6.06/6.28  # Unit Clause-clause subsumption calls : 737
% 6.06/6.28  # Rewrite failures with RHS unbound    : 0
% 6.06/6.28  # BW rewrite match attempts            : 11509
% 6.06/6.28  # BW rewrite match successes           : 11
% 6.06/6.28  # Condensation attempts                : 0
% 6.06/6.28  # Condensation successes               : 0
% 6.06/6.28  # Termbank termtop insertions          : 13928289
% 6.06/6.29  
% 6.06/6.29  # -------------------------------------------------
% 6.06/6.29  # User time                : 5.848 s
% 6.06/6.29  # System time              : 0.096 s
% 6.06/6.29  # Total time               : 5.944 s
% 6.06/6.29  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
