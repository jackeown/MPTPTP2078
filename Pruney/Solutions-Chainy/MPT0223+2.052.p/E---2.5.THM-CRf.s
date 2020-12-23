%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 609 expanded)
%              Number of clauses        :   32 ( 235 expanded)
%              Number of leaves         :   14 ( 185 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 675 expanded)
%              Number of equality atoms :   96 ( 653 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_14,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X10,X11)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k2_xboole_0(X8,X9)) = X8 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X36,X37,X38,X39] : k2_enumset1(X36,X37,X38,X39) = k2_xboole_0(k1_enumset1(X36,X37,X38),k1_tarski(X39)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_25,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X46,X47,X48,X49] : k3_enumset1(X46,X46,X47,X48,X49) = k2_enumset1(X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_30,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18]),c_0_22])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_33,plain,(
    ! [X33,X34,X35] : k1_enumset1(X33,X34,X35) = k1_enumset1(X35,X34,X33) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X26
        | X27 != k1_tarski(X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_tarski(X26) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | esk2_2(X30,X31) != X30
        | X31 = k1_tarski(X30) )
      & ( r2_hidden(esk2_2(X30,X31),X31)
        | esk2_2(X30,X31) = X30
        | X31 = k1_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_22]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_48,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])).

fof(c_0_50,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X15
        | X19 = X16
        | X19 = X17
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X15
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( esk1_4(X21,X22,X23,X24) != X21
        | ~ r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk1_4(X21,X22,X23,X24) != X22
        | ~ r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk1_4(X21,X22,X23,X24) != X23
        | ~ r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | esk1_4(X21,X22,X23,X24) = X21
        | esk1_4(X21,X22,X23,X24) = X22
        | esk1_4(X21,X22,X23,X24) = X23
        | X24 = k1_enumset1(X21,X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_51,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X1) = k3_enumset1(esk3_0,esk3_0,esk4_0,esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_49]),c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk4_0,esk4_0,esk4_0) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_37]),c_0_38])).

cnf(c_0_57,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_55])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.21/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.39  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.21/0.39  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.21/0.39  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 0.21/0.39  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.21/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.39  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 0.21/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.21/0.39  fof(c_0_14, plain, ![X13, X14]:k2_xboole_0(X13,X14)=k5_xboole_0(X13,k4_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.39  fof(c_0_15, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.39  fof(c_0_16, plain, ![X10, X11]:k4_xboole_0(X10,k2_xboole_0(X10,X11))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.21/0.39  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  fof(c_0_19, plain, ![X8, X9]:k3_xboole_0(X8,k2_xboole_0(X8,X9))=X8, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.21/0.39  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 0.21/0.39  cnf(c_0_21, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.39  cnf(c_0_23, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  fof(c_0_24, plain, ![X36, X37, X38, X39]:k2_enumset1(X36,X37,X38,X39)=k2_xboole_0(k1_enumset1(X36,X37,X38),k1_tarski(X39)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.21/0.39  fof(c_0_25, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_26, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_27, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.39  fof(c_0_28, plain, ![X46, X47, X48, X49]:k3_enumset1(X46,X46,X47,X48,X49)=k2_enumset1(X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.39  fof(c_0_29, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.21/0.39  fof(c_0_30, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.39  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_18]), c_0_22])).
% 0.21/0.39  cnf(c_0_32, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 0.21/0.39  fof(c_0_33, plain, ![X33, X34, X35]:k1_enumset1(X33,X34,X35)=k1_enumset1(X35,X34,X33), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 0.21/0.39  cnf(c_0_34, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_40, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.39  cnf(c_0_41, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.39  cnf(c_0_42, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  fof(c_0_43, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|X28=X26|X27!=k1_tarski(X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_tarski(X26)))&((~r2_hidden(esk2_2(X30,X31),X31)|esk2_2(X30,X31)!=X30|X31=k1_tarski(X30))&(r2_hidden(esk2_2(X30,X31),X31)|esk2_2(X30,X31)=X30|X31=k1_tarski(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.39  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_22]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38])).
% 0.21/0.39  cnf(c_0_46, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.39  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.21/0.39  cnf(c_0_48, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_enumset1(esk3_0,esk3_0,esk3_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.39  fof(c_0_50, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X19,X18)|(X19=X15|X19=X16|X19=X17)|X18!=k1_enumset1(X15,X16,X17))&(((X20!=X15|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))&(X20!=X16|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17)))&(X20!=X17|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))))&((((esk1_4(X21,X22,X23,X24)!=X21|~r2_hidden(esk1_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23))&(esk1_4(X21,X22,X23,X24)!=X22|~r2_hidden(esk1_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(esk1_4(X21,X22,X23,X24)!=X23|~r2_hidden(esk1_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(r2_hidden(esk1_4(X21,X22,X23,X24),X24)|(esk1_4(X21,X22,X23,X24)=X21|esk1_4(X21,X22,X23,X24)=X22|esk1_4(X21,X22,X23,X24)=X23)|X24=k1_enumset1(X21,X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.21/0.39  cnf(c_0_51, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X1)=k3_enumset1(esk3_0,esk3_0,esk4_0,esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_49]), c_0_44])).
% 0.21/0.39  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.39  cnf(c_0_54, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_51])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk4_0,esk4_0,esk4_0)=k3_enumset1(esk3_0,esk3_0,esk3_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_49, c_0_52])).
% 0.21/0.39  cnf(c_0_56, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_37]), c_0_38])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_55])).
% 0.21/0.39  cnf(c_0_58, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 61
% 0.21/0.39  # Proof object clause steps            : 32
% 0.21/0.39  # Proof object formula steps           : 29
% 0.21/0.39  # Proof object conjectures             : 11
% 0.21/0.39  # Proof object clause conjectures      : 8
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 15
% 0.21/0.39  # Proof object initial formulas used   : 14
% 0.21/0.39  # Proof object generating inferences   : 5
% 0.21/0.39  # Proof object simplifying inferences  : 48
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 14
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 25
% 0.21/0.39  # Removed in clause preprocessing      : 6
% 0.21/0.39  # Initial clauses in saturation        : 19
% 0.21/0.39  # Processed clauses                    : 85
% 0.21/0.39  # ...of these trivial                  : 6
% 0.21/0.39  # ...subsumed                          : 22
% 0.21/0.39  # ...remaining for further processing  : 57
% 0.21/0.39  # Other redundant clauses eliminated   : 10
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 3
% 0.21/0.39  # Generated clauses                    : 217
% 0.21/0.39  # ...of the previous two non-trivial   : 111
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 211
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 10
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 30
% 0.21/0.39  #    Positive orientable unit clauses  : 15
% 0.21/0.39  #    Positive unorientable unit clauses: 5
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 9
% 0.21/0.39  # Current number of unprocessed clauses: 59
% 0.21/0.39  # ...number of literals in the above   : 97
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 27
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 26
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 24
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.21/0.39  # Unit Clause-clause subsumption calls : 28
% 0.21/0.39  # Rewrite failures with RHS unbound    : 20
% 0.21/0.39  # BW rewrite match attempts            : 121
% 0.21/0.39  # BW rewrite match successes           : 63
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 3408
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.032 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.036 s
% 0.21/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
