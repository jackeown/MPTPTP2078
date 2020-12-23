%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:42 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 111 expanded)
%              Number of clauses        :   20 (  39 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 185 expanded)
%              Number of equality atoms :   59 ( 126 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

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

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
          & X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t16_zfmisc_1])).

fof(c_0_13,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))
    & esk3_0 = esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X24] : k2_tarski(X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X30,X31,X32,X33] : k3_enumset1(X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X34,X35,X36,X37,X38] : k4_enumset1(X34,X34,X35,X36,X37,X38) = k3_enumset1(X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_19,plain,(
    ! [X39,X40,X41,X42,X43,X44] : k5_enumset1(X39,X39,X40,X41,X42,X43,X44) = k4_enumset1(X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] : k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51) = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_21,plain,(
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
      & ( esk2_4(X19,X20,X21,X22) != X19
        | ~ r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk2_4(X19,X20,X21,X22) != X20
        | ~ r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk2_4(X19,X20,X21,X22) != X21
        | ~ r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | esk2_4(X19,X20,X21,X22) = X19
        | esk2_4(X19,X20,X21,X22) = X20
        | esk2_4(X19,X20,X21,X22) = X21
        | X22 = k1_enumset1(X19,X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X12] :
      ( ( r1_xboole_0(X12,X12)
        | X12 != k1_xboole_0 )
      & ( X12 = k1_xboole_0
        | ~ r1_xboole_0(X12,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

fof(c_0_37,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.039 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t16_zfmisc_1, conjecture, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.14/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.14/0.39  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.14/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.39  fof(c_0_12, negated_conjecture, ~(![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2))), inference(assume_negation,[status(cth)],[t16_zfmisc_1])).
% 0.14/0.39  fof(c_0_13, negated_conjecture, (r1_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))&esk3_0=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.14/0.39  fof(c_0_14, plain, ![X24]:k2_tarski(X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.39  fof(c_0_15, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.39  fof(c_0_16, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.39  fof(c_0_17, plain, ![X30, X31, X32, X33]:k3_enumset1(X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.39  fof(c_0_18, plain, ![X34, X35, X36, X37, X38]:k4_enumset1(X34,X34,X35,X36,X37,X38)=k3_enumset1(X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.39  fof(c_0_19, plain, ![X39, X40, X41, X42, X43, X44]:k5_enumset1(X39,X39,X40,X41,X42,X43,X44)=k4_enumset1(X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.39  fof(c_0_20, plain, ![X45, X46, X47, X48, X49, X50, X51]:k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51)=k5_enumset1(X45,X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.39  fof(c_0_21, plain, ![X13, X14, X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X17,X16)|(X17=X13|X17=X14|X17=X15)|X16!=k1_enumset1(X13,X14,X15))&(((X18!=X13|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))&(X18!=X14|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15)))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))))&((((esk2_4(X19,X20,X21,X22)!=X19|~r2_hidden(esk2_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21))&(esk2_4(X19,X20,X21,X22)!=X20|~r2_hidden(esk2_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(esk2_4(X19,X20,X21,X22)!=X21|~r2_hidden(esk2_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(r2_hidden(esk2_4(X19,X20,X21,X22),X22)|(esk2_4(X19,X20,X21,X22)=X19|esk2_4(X19,X20,X21,X22)=X20|esk2_4(X19,X20,X21,X22)=X21)|X22=k1_enumset1(X19,X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (r1_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_27, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_28, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_29, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  fof(c_0_31, plain, ![X12]:((r1_xboole_0(X12,X12)|X12!=k1_xboole_0)&(X12=k1_xboole_0|~r1_xboole_0(X12,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (r1_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (esk3_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.14/0.39  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (r1_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.14/0.39  fof(c_0_37, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.39  cnf(c_0_38, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.39  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.39  cnf(c_0_42, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 44
% 0.14/0.39  # Proof object clause steps            : 20
% 0.14/0.39  # Proof object formula steps           : 24
% 0.14/0.39  # Proof object conjectures             : 10
% 0.14/0.39  # Proof object clause conjectures      : 7
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 13
% 0.14/0.39  # Proof object initial formulas used   : 12
% 0.14/0.39  # Proof object generating inferences   : 3
% 0.14/0.39  # Proof object simplifying inferences  : 31
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 12
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 22
% 0.14/0.39  # Removed in clause preprocessing      : 7
% 0.14/0.39  # Initial clauses in saturation        : 15
% 0.14/0.39  # Processed clauses                    : 29
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 29
% 0.14/0.39  # Other redundant clauses eliminated   : 8
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 1
% 0.14/0.39  # Generated clauses                    : 9
% 0.14/0.39  # ...of the previous two non-trivial   : 8
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 4
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 8
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 8
% 0.14/0.39  #    Positive orientable unit clauses  : 6
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 2
% 0.14/0.39  # Current number of unprocessed clauses: 9
% 0.14/0.39  # ...number of literals in the above   : 23
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 23
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 6
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 6
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.39  # Unit Clause-clause subsumption calls : 0
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 4
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1185
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.006 s
% 0.14/0.39  # Total time               : 0.045 s
% 0.14/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
