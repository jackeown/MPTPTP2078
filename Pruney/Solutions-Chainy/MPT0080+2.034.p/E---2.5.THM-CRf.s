%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:11 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 159 expanded)
%              Number of clauses        :   41 (  72 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 253 expanded)
%              Number of equality atoms :   49 ( 137 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_14,plain,(
    ! [X22,X23] : k2_xboole_0(X22,k4_xboole_0(X23,X22)) = k2_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,X21) != k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | k4_xboole_0(X20,X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    & r1_xboole_0(esk3_0,esk5_0)
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_17,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_19,plain,(
    ! [X25,X26] : k4_xboole_0(k2_xboole_0(X25,X26),X26) = k4_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_27,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_24])).

fof(c_0_31,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X32] : r1_xboole_0(X32,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_23])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_39])])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),k2_xboole_0(esk5_0,esk4_0)) = k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

fof(c_0_44,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_39])])).

fof(c_0_47,plain,(
    ! [X27,X28,X29] : k4_xboole_0(k4_xboole_0(X27,X28),X29) = k4_xboole_0(X27,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_48,plain,(
    ! [X33] :
      ( ( r1_xboole_0(X33,X33)
        | X33 != k1_xboole_0 )
      & ( X33 = k1_xboole_0
        | ~ r1_xboole_0(X33,X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_36]),c_0_52])])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_41]),c_0_56])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.50/0.68  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.50/0.68  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.50/0.68  #
% 0.50/0.68  # Preprocessing time       : 0.027 s
% 0.50/0.68  # Presaturation interreduction done
% 0.50/0.68  
% 0.50/0.68  # Proof found!
% 0.50/0.68  # SZS status Theorem
% 0.50/0.68  # SZS output start CNFRefutation
% 0.50/0.68  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.50/0.68  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.50/0.68  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.50/0.68  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.50/0.68  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.50/0.68  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.50/0.68  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.50/0.68  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.50/0.68  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.50/0.68  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.50/0.68  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.50/0.68  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.50/0.68  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.50/0.68  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.50/0.68  fof(c_0_14, plain, ![X22, X23]:k2_xboole_0(X22,k4_xboole_0(X23,X22))=k2_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.50/0.68  fof(c_0_15, plain, ![X20, X21]:((k4_xboole_0(X20,X21)!=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|k4_xboole_0(X20,X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.50/0.68  fof(c_0_16, negated_conjecture, ((r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))&r1_xboole_0(esk3_0,esk5_0))&~r1_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.50/0.68  fof(c_0_17, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.50/0.68  fof(c_0_18, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.50/0.68  fof(c_0_19, plain, ![X25, X26]:k4_xboole_0(k2_xboole_0(X25,X26),X26)=k4_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.50/0.68  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.68  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.68  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.68  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.68  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.68  cnf(c_0_25, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.50/0.68  fof(c_0_26, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.50/0.68  fof(c_0_27, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.50/0.68  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.50/0.68  cnf(c_0_29, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.50/0.68  cnf(c_0_30, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_24])).
% 0.50/0.68  fof(c_0_31, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.50/0.68  cnf(c_0_32, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.68  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.50/0.68  fof(c_0_34, plain, ![X32]:r1_xboole_0(X32,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.50/0.68  cnf(c_0_35, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k2_xboole_0(k1_xboole_0,k2_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23]), c_0_23])).
% 0.50/0.68  cnf(c_0_36, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_30])).
% 0.50/0.68  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.50/0.68  cnf(c_0_38, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.50/0.68  cnf(c_0_39, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.50/0.68  cnf(c_0_40, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k2_xboole_0(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.50/0.68  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_33])).
% 0.50/0.68  cnf(c_0_42, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_24]), c_0_39])])).
% 0.50/0.68  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),k2_xboole_0(esk5_0,esk4_0))=k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_40])).
% 0.50/0.68  fof(c_0_44, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.50/0.68  cnf(c_0_45, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.68  cnf(c_0_46, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_24]), c_0_39])])).
% 0.50/0.68  fof(c_0_47, plain, ![X27, X28, X29]:k4_xboole_0(k4_xboole_0(X27,X28),X29)=k4_xboole_0(X27,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.50/0.68  fof(c_0_48, plain, ![X33]:((r1_xboole_0(X33,X33)|X33!=k1_xboole_0)&(X33=k1_xboole_0|~r1_xboole_0(X33,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.50/0.68  cnf(c_0_49, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.50/0.68  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.50/0.68  cnf(c_0_51, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.50/0.68  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.50/0.68  cnf(c_0_53, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.50/0.68  cnf(c_0_54, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.50/0.68  cnf(c_0_55, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.50/0.68  cnf(c_0_56, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_36]), c_0_52])])).
% 0.50/0.68  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_53])).
% 0.50/0.68  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.50/0.68  cnf(c_0_59, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_41]), c_0_56])).
% 0.50/0.68  cnf(c_0_60, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_28, c_0_30])).
% 0.50/0.68  cnf(c_0_61, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.50/0.68  cnf(c_0_62, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k1_xboole_0|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_59, c_0_23])).
% 0.50/0.68  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0))=esk4_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.50/0.68  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.68  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.50/0.68  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.68  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_65]), c_0_66]), ['proof']).
% 0.50/0.68  # SZS output end CNFRefutation
% 0.50/0.68  # Proof object total steps             : 68
% 0.50/0.68  # Proof object clause steps            : 41
% 0.50/0.68  # Proof object formula steps           : 27
% 0.50/0.68  # Proof object conjectures             : 17
% 0.50/0.68  # Proof object clause conjectures      : 14
% 0.50/0.68  # Proof object formula conjectures     : 3
% 0.50/0.68  # Proof object initial clauses used    : 16
% 0.50/0.68  # Proof object initial formulas used   : 13
% 0.50/0.68  # Proof object generating inferences   : 20
% 0.50/0.68  # Proof object simplifying inferences  : 18
% 0.50/0.68  # Training examples: 0 positive, 0 negative
% 0.50/0.68  # Parsed axioms                        : 13
% 0.50/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.68  # Initial clauses                      : 21
% 0.50/0.68  # Removed in clause preprocessing      : 1
% 0.50/0.68  # Initial clauses in saturation        : 20
% 0.50/0.68  # Processed clauses                    : 4946
% 0.50/0.68  # ...of these trivial                  : 74
% 0.50/0.68  # ...subsumed                          : 4247
% 0.50/0.68  # ...remaining for further processing  : 625
% 0.50/0.68  # Other redundant clauses eliminated   : 0
% 0.50/0.68  # Clauses deleted for lack of memory   : 0
% 0.50/0.68  # Backward-subsumed                    : 27
% 0.50/0.68  # Backward-rewritten                   : 51
% 0.50/0.68  # Generated clauses                    : 34149
% 0.50/0.68  # ...of the previous two non-trivial   : 29235
% 0.50/0.68  # Contextual simplify-reflections      : 3
% 0.50/0.68  # Paramodulations                      : 34148
% 0.50/0.68  # Factorizations                       : 0
% 0.50/0.68  # Equation resolutions                 : 0
% 0.50/0.68  # Propositional unsat checks           : 0
% 0.50/0.68  #    Propositional check models        : 0
% 0.50/0.68  #    Propositional check unsatisfiable : 0
% 0.50/0.68  #    Propositional clauses             : 0
% 0.50/0.68  #    Propositional clauses after purity: 0
% 0.50/0.68  #    Propositional unsat core size     : 0
% 0.50/0.68  #    Propositional preprocessing time  : 0.000
% 0.50/0.68  #    Propositional encoding time       : 0.000
% 0.50/0.68  #    Propositional solver time         : 0.000
% 0.50/0.68  #    Success case prop preproc time    : 0.000
% 0.50/0.68  #    Success case prop encoding time   : 0.000
% 0.50/0.68  #    Success case prop solver time     : 0.000
% 0.50/0.68  # Current number of processed clauses  : 526
% 0.50/0.68  #    Positive orientable unit clauses  : 102
% 0.50/0.68  #    Positive unorientable unit clauses: 3
% 0.50/0.68  #    Negative unit clauses             : 81
% 0.50/0.68  #    Non-unit-clauses                  : 340
% 0.50/0.68  # Current number of unprocessed clauses: 24147
% 0.50/0.68  # ...number of literals in the above   : 53586
% 0.50/0.68  # Current number of archived formulas  : 0
% 0.50/0.68  # Current number of archived clauses   : 100
% 0.50/0.68  # Clause-clause subsumption calls (NU) : 12600
% 0.50/0.68  # Rec. Clause-clause subsumption calls : 8469
% 0.50/0.68  # Non-unit clause-clause subsumptions  : 1252
% 0.50/0.68  # Unit Clause-clause subsumption calls : 9156
% 0.50/0.68  # Rewrite failures with RHS unbound    : 0
% 0.50/0.68  # BW rewrite match attempts            : 403
% 0.50/0.68  # BW rewrite match successes           : 99
% 0.50/0.68  # Condensation attempts                : 0
% 0.50/0.68  # Condensation successes               : 0
% 0.50/0.68  # Termbank termtop insertions          : 416776
% 0.50/0.68  
% 0.50/0.68  # -------------------------------------------------
% 0.50/0.68  # User time                : 0.323 s
% 0.50/0.68  # System time              : 0.015 s
% 0.50/0.68  # Total time               : 0.338 s
% 0.50/0.68  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
