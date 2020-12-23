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
% DateTime   : Thu Dec  3 10:44:40 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 389 expanded)
%              Number of clauses        :   37 ( 161 expanded)
%              Number of leaves         :   12 ( 110 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 518 expanded)
%              Number of equality atoms :   68 ( 413 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_12,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X36,X35)
        | X36 = X34
        | X35 != k1_tarski(X34) )
      & ( X37 != X34
        | r2_hidden(X37,X35)
        | X35 != k1_tarski(X34) )
      & ( ~ r2_hidden(esk3_2(X38,X39),X39)
        | esk3_2(X38,X39) != X38
        | X39 = k1_tarski(X38) )
      & ( r2_hidden(esk3_2(X38,X39),X39)
        | esk3_2(X38,X39) = X38
        | X39 = k1_tarski(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X41] : k2_tarski(X41,X41) = k1_tarski(X41) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X42,X43] : k1_enumset1(X42,X42,X43) = k2_tarski(X42,X43) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X44,X45,X46] : k2_enumset1(X44,X44,X45,X46) = k1_enumset1(X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_18,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_19,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    & k3_xboole_0(esk5_0,esk6_0) = k1_tarski(esk7_0)
    & r2_hidden(esk7_0,esk4_0)
    & k3_xboole_0(esk4_0,esk6_0) != k1_tarski(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_24,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k3_xboole_0(X30,X31)) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] : k3_xboole_0(k3_xboole_0(X25,X26),X27) = k3_xboole_0(X25,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X22] : k3_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) = k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_21]),c_0_22]),c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_37])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k4_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))) = k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))
    | esk1_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1) = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_26]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) != k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_20]),c_0_21]),c_0_22]),c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))) = k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))
    | r1_tarski(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1))) = k4_xboole_0(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_53]),c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) != k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52]),c_0_57]),c_0_52]),c_0_58]),c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_60]),c_0_45]),c_0_52]),c_0_57]),c_0_52]),c_0_58]),c_0_59]),
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
% 0.12/0.33  % DateTime   : Tue Dec  1 19:17:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 7.40/7.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 7.40/7.63  # and selection function SelectCQArNTNpEqFirst.
% 7.40/7.63  #
% 7.40/7.63  # Preprocessing time       : 0.027 s
% 7.40/7.63  # Presaturation interreduction done
% 7.40/7.63  
% 7.40/7.63  # Proof found!
% 7.40/7.63  # SZS status Theorem
% 7.40/7.63  # SZS output start CNFRefutation
% 7.40/7.63  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.40/7.63  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.40/7.63  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.40/7.63  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.40/7.63  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 7.40/7.63  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.40/7.63  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.40/7.63  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.40/7.63  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.40/7.63  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.40/7.63  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.40/7.63  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.40/7.63  fof(c_0_12, plain, ![X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X36,X35)|X36=X34|X35!=k1_tarski(X34))&(X37!=X34|r2_hidden(X37,X35)|X35!=k1_tarski(X34)))&((~r2_hidden(esk3_2(X38,X39),X39)|esk3_2(X38,X39)!=X38|X39=k1_tarski(X38))&(r2_hidden(esk3_2(X38,X39),X39)|esk3_2(X38,X39)=X38|X39=k1_tarski(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 7.40/7.63  fof(c_0_13, plain, ![X41]:k2_tarski(X41,X41)=k1_tarski(X41), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 7.40/7.63  fof(c_0_14, plain, ![X42, X43]:k1_enumset1(X42,X42,X43)=k2_tarski(X42,X43), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 7.40/7.63  fof(c_0_15, plain, ![X44, X45, X46]:k2_enumset1(X44,X44,X45,X46)=k1_enumset1(X44,X45,X46), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 7.40/7.63  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 7.40/7.63  fof(c_0_17, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 7.40/7.63  fof(c_0_18, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 7.40/7.63  cnf(c_0_19, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 7.40/7.63  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.40/7.63  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 7.40/7.63  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 7.40/7.63  fof(c_0_23, negated_conjecture, (((r1_tarski(esk4_0,esk5_0)&k3_xboole_0(esk5_0,esk6_0)=k1_tarski(esk7_0))&r2_hidden(esk7_0,esk4_0))&k3_xboole_0(esk4_0,esk6_0)!=k1_tarski(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 7.40/7.63  fof(c_0_24, plain, ![X30, X31]:k4_xboole_0(X30,k3_xboole_0(X30,X31))=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 7.40/7.63  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 7.40/7.63  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.40/7.63  cnf(c_0_27, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 7.40/7.63  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.40/7.63  fof(c_0_29, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 7.40/7.63  fof(c_0_30, plain, ![X25, X26, X27]:k3_xboole_0(k3_xboole_0(X25,X26),X27)=k3_xboole_0(X25,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 7.40/7.63  cnf(c_0_31, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.40/7.63  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 7.40/7.63  cnf(c_0_33, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.40/7.63  fof(c_0_34, plain, ![X22]:k3_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 7.40/7.63  cnf(c_0_35, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_27])).
% 7.40/7.63  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_21]), c_0_22]), c_0_26])).
% 7.40/7.63  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.40/7.63  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.40/7.63  fof(c_0_39, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 7.40/7.63  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_26])).
% 7.40/7.63  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))=esk4_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 7.40/7.63  cnf(c_0_42, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.40/7.63  cnf(c_0_43, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 7.40/7.63  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_32, c_0_37])).
% 7.40/7.63  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 7.40/7.63  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 7.40/7.63  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=k4_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 7.40/7.63  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_42, c_0_26])).
% 7.40/7.63  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.40/7.63  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.40/7.63  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1))))=k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))|esk1_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1)=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 7.40/7.63  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_26]), c_0_26])).
% 7.40/7.63  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_47]), c_0_48]), c_0_48])).
% 7.40/7.63  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))!=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_20]), c_0_21]), c_0_22]), c_0_26])).
% 7.40/7.63  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1))))=k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))|r1_tarski(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1)|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 7.40/7.63  cnf(c_0_56, negated_conjecture, (r2_hidden(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.40/7.63  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_45])).
% 7.40/7.63  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)))=k4_xboole_0(esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_53]), c_0_40])).
% 7.40/7.63  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))!=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[c_0_54, c_0_36])).
% 7.40/7.63  cnf(c_0_60, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_52]), c_0_57]), c_0_52]), c_0_58]), c_0_59])).
% 7.40/7.63  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_60]), c_0_45]), c_0_52]), c_0_57]), c_0_52]), c_0_58]), c_0_59]), ['proof']).
% 7.40/7.63  # SZS output end CNFRefutation
% 7.40/7.63  # Proof object total steps             : 62
% 7.40/7.63  # Proof object clause steps            : 37
% 7.40/7.63  # Proof object formula steps           : 25
% 7.40/7.63  # Proof object conjectures             : 19
% 7.40/7.63  # Proof object clause conjectures      : 16
% 7.40/7.63  # Proof object formula conjectures     : 3
% 7.40/7.63  # Proof object initial clauses used    : 16
% 7.40/7.63  # Proof object initial formulas used   : 12
% 7.40/7.63  # Proof object generating inferences   : 11
% 7.40/7.63  # Proof object simplifying inferences  : 37
% 7.40/7.63  # Training examples: 0 positive, 0 negative
% 7.40/7.63  # Parsed axioms                        : 14
% 7.40/7.63  # Removed by relevancy pruning/SinE    : 0
% 7.40/7.63  # Initial clauses                      : 29
% 7.40/7.63  # Removed in clause preprocessing      : 4
% 7.40/7.63  # Initial clauses in saturation        : 25
% 7.40/7.63  # Processed clauses                    : 34140
% 7.40/7.63  # ...of these trivial                  : 1866
% 7.40/7.63  # ...subsumed                          : 28360
% 7.40/7.63  # ...remaining for further processing  : 3914
% 7.40/7.63  # Other redundant clauses eliminated   : 88
% 7.40/7.63  # Clauses deleted for lack of memory   : 0
% 7.40/7.63  # Backward-subsumed                    : 106
% 7.40/7.63  # Backward-rewritten                   : 1616
% 7.40/7.63  # Generated clauses                    : 734348
% 7.40/7.63  # ...of the previous two non-trivial   : 605132
% 7.40/7.63  # Contextual simplify-reflections      : 22
% 7.40/7.63  # Paramodulations                      : 733900
% 7.40/7.63  # Factorizations                       : 361
% 7.40/7.63  # Equation resolutions                 : 88
% 7.40/7.63  # Propositional unsat checks           : 0
% 7.40/7.63  #    Propositional check models        : 0
% 7.40/7.63  #    Propositional check unsatisfiable : 0
% 7.40/7.63  #    Propositional clauses             : 0
% 7.40/7.63  #    Propositional clauses after purity: 0
% 7.40/7.63  #    Propositional unsat core size     : 0
% 7.40/7.63  #    Propositional preprocessing time  : 0.000
% 7.40/7.63  #    Propositional encoding time       : 0.000
% 7.40/7.63  #    Propositional solver time         : 0.000
% 7.40/7.63  #    Success case prop preproc time    : 0.000
% 7.40/7.63  #    Success case prop encoding time   : 0.000
% 7.40/7.63  #    Success case prop solver time     : 0.000
% 7.40/7.63  # Current number of processed clauses  : 2161
% 7.40/7.63  #    Positive orientable unit clauses  : 571
% 7.40/7.63  #    Positive unorientable unit clauses: 14
% 7.40/7.63  #    Negative unit clauses             : 395
% 7.40/7.63  #    Non-unit-clauses                  : 1181
% 7.40/7.63  # Current number of unprocessed clauses: 564785
% 7.40/7.63  # ...number of literals in the above   : 1606143
% 7.40/7.63  # Current number of archived formulas  : 0
% 7.40/7.63  # Current number of archived clauses   : 1750
% 7.40/7.63  # Clause-clause subsumption calls (NU) : 220927
% 7.40/7.63  # Rec. Clause-clause subsumption calls : 165071
% 7.40/7.63  # Non-unit clause-clause subsumptions  : 6908
% 7.40/7.63  # Unit Clause-clause subsumption calls : 245212
% 7.40/7.63  # Rewrite failures with RHS unbound    : 121
% 7.40/7.63  # BW rewrite match attempts            : 144822
% 7.40/7.63  # BW rewrite match successes           : 1060
% 7.40/7.63  # Condensation attempts                : 0
% 7.40/7.63  # Condensation successes               : 0
% 7.40/7.63  # Termbank termtop insertions          : 19399921
% 7.49/7.66  
% 7.49/7.66  # -------------------------------------------------
% 7.49/7.66  # User time                : 7.058 s
% 7.49/7.66  # System time              : 0.271 s
% 7.49/7.66  # Total time               : 7.329 s
% 7.49/7.66  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
