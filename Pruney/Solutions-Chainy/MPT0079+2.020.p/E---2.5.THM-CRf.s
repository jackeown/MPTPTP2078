%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:02 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 227 expanded)
%              Number of clauses        :   42 ( 101 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 384 expanded)
%              Number of equality atoms :   57 ( 215 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(c_0_15,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_16,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(X18,X19) != k1_xboole_0
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | k4_xboole_0(X18,X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_18,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_27,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_29,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k3_xboole_0(X30,X31)) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,k2_xboole_0(X28,X29))
      | r1_tarski(k4_xboole_0(X27,X28),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_34,plain,(
    ! [X37,X38] : r1_tarski(X37,k2_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk6_0,k4_xboole_0(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_20]),c_0_20])).

fof(c_0_41,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k2_xboole_0(X20,X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

fof(c_0_52,plain,(
    ! [X34,X35,X36] : k2_xboole_0(k2_xboole_0(X34,X35),X36) = k2_xboole_0(X34,k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

fof(c_0_55,plain,(
    ! [X9] : k2_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_57,plain,(
    ! [X25,X26] : k4_xboole_0(k2_xboole_0(X25,X26),X26) = k4_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_36])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk5_0,k4_xboole_0(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_56])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,X1)) = k2_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_44])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_44]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_65]),c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_62]),c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_69]),c_0_70]),c_0_47]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:25:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.22/0.46  # and selection function SelectLargestOrientable.
% 0.22/0.46  #
% 0.22/0.46  # Preprocessing time       : 0.026 s
% 0.22/0.46  # Presaturation interreduction done
% 0.22/0.46  
% 0.22/0.46  # Proof found!
% 0.22/0.46  # SZS status Theorem
% 0.22/0.46  # SZS output start CNFRefutation
% 0.22/0.46  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.22/0.46  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.22/0.46  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.22/0.46  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.22/0.46  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.22/0.46  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.22/0.46  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.22/0.46  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.22/0.46  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.22/0.46  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.22/0.46  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.22/0.46  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.22/0.46  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.22/0.46  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.22/0.46  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.22/0.46  fof(c_0_15, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.22/0.46  fof(c_0_16, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.22/0.46  fof(c_0_17, plain, ![X18, X19]:((k4_xboole_0(X18,X19)!=k1_xboole_0|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|k4_xboole_0(X18,X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.22/0.46  fof(c_0_18, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.22/0.46  cnf(c_0_19, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.46  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.46  cnf(c_0_21, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.46  cnf(c_0_22, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.46  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.22/0.46  cnf(c_0_24, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.22/0.46  cnf(c_0_25, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.22/0.46  fof(c_0_26, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.22/0.46  fof(c_0_27, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.22/0.46  fof(c_0_28, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.22/0.46  fof(c_0_29, plain, ![X30, X31]:k4_xboole_0(X30,k3_xboole_0(X30,X31))=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.22/0.46  cnf(c_0_30, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.22/0.46  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.22/0.46  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.22/0.46  fof(c_0_33, plain, ![X27, X28, X29]:(~r1_tarski(X27,k2_xboole_0(X28,X29))|r1_tarski(k4_xboole_0(X27,X28),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.22/0.46  fof(c_0_34, plain, ![X37, X38]:r1_tarski(X37,k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.22/0.46  cnf(c_0_35, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.22/0.46  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.22/0.46  cnf(c_0_37, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.22/0.46  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.46  cnf(c_0_39, negated_conjecture, (r1_tarski(esk6_0,k4_xboole_0(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.22/0.46  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_20]), c_0_20])).
% 0.22/0.46  fof(c_0_41, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.22/0.46  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.22/0.46  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.22/0.46  cnf(c_0_44, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.22/0.46  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_20])).
% 0.22/0.46  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.22/0.46  cnf(c_0_47, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.22/0.46  fof(c_0_48, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k2_xboole_0(X20,X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.22/0.46  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_42, c_0_36])).
% 0.22/0.46  cnf(c_0_50, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.22/0.46  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.22/0.46  fof(c_0_52, plain, ![X34, X35, X36]:k2_xboole_0(k2_xboole_0(X34,X35),X36)=k2_xboole_0(X34,k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.22/0.46  cnf(c_0_53, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.22/0.46  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.22/0.46  fof(c_0_55, plain, ![X9]:k2_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.22/0.46  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.22/0.46  fof(c_0_57, plain, ![X25, X26]:k4_xboole_0(k2_xboole_0(X25,X26),X26)=k4_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.22/0.46  cnf(c_0_58, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.22/0.46  cnf(c_0_59, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_36])).
% 0.22/0.46  cnf(c_0_60, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.22/0.46  cnf(c_0_61, negated_conjecture, (r1_tarski(esk5_0,k4_xboole_0(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_56])).
% 0.22/0.46  cnf(c_0_62, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.22/0.46  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,X1))=k2_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.22/0.46  cnf(c_0_64, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_60])).
% 0.22/0.46  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_61])).
% 0.22/0.46  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_44])).
% 0.22/0.46  cnf(c_0_67, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=k2_xboole_0(esk5_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_44]), c_0_64])).
% 0.22/0.46  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_65]), c_0_47])).
% 0.22/0.46  cnf(c_0_69, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_62]), c_0_68])).
% 0.22/0.46  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_54])).
% 0.22/0.46  cnf(c_0_71, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.22/0.46  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_69]), c_0_70]), c_0_47]), c_0_71]), ['proof']).
% 0.22/0.46  # SZS output end CNFRefutation
% 0.22/0.46  # Proof object total steps             : 73
% 0.22/0.46  # Proof object clause steps            : 42
% 0.22/0.46  # Proof object formula steps           : 31
% 0.22/0.46  # Proof object conjectures             : 23
% 0.22/0.46  # Proof object clause conjectures      : 20
% 0.22/0.46  # Proof object formula conjectures     : 3
% 0.22/0.46  # Proof object initial clauses used    : 19
% 0.22/0.46  # Proof object initial formulas used   : 15
% 0.22/0.46  # Proof object generating inferences   : 18
% 0.22/0.46  # Proof object simplifying inferences  : 17
% 0.22/0.46  # Training examples: 0 positive, 0 negative
% 0.22/0.46  # Parsed axioms                        : 16
% 0.22/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.46  # Initial clauses                      : 21
% 0.22/0.46  # Removed in clause preprocessing      : 1
% 0.22/0.47  # Initial clauses in saturation        : 20
% 0.22/0.47  # Processed clauses                    : 821
% 0.22/0.47  # ...of these trivial                  : 39
% 0.22/0.47  # ...subsumed                          : 458
% 0.22/0.47  # ...remaining for further processing  : 324
% 0.22/0.47  # Other redundant clauses eliminated   : 12
% 0.22/0.47  # Clauses deleted for lack of memory   : 0
% 0.22/0.47  # Backward-subsumed                    : 33
% 0.22/0.47  # Backward-rewritten                   : 114
% 0.22/0.47  # Generated clauses                    : 7598
% 0.22/0.47  # ...of the previous two non-trivial   : 5804
% 0.22/0.47  # Contextual simplify-reflections      : 3
% 0.22/0.47  # Paramodulations                      : 7586
% 0.22/0.47  # Factorizations                       : 0
% 0.22/0.47  # Equation resolutions                 : 12
% 0.22/0.47  # Propositional unsat checks           : 0
% 0.22/0.47  #    Propositional check models        : 0
% 0.22/0.47  #    Propositional check unsatisfiable : 0
% 0.22/0.47  #    Propositional clauses             : 0
% 0.22/0.47  #    Propositional clauses after purity: 0
% 0.22/0.47  #    Propositional unsat core size     : 0
% 0.22/0.47  #    Propositional preprocessing time  : 0.000
% 0.22/0.47  #    Propositional encoding time       : 0.000
% 0.22/0.47  #    Propositional solver time         : 0.000
% 0.22/0.47  #    Success case prop preproc time    : 0.000
% 0.22/0.47  #    Success case prop encoding time   : 0.000
% 0.22/0.47  #    Success case prop solver time     : 0.000
% 0.22/0.47  # Current number of processed clauses  : 157
% 0.22/0.47  #    Positive orientable unit clauses  : 71
% 0.22/0.47  #    Positive unorientable unit clauses: 4
% 0.22/0.47  #    Negative unit clauses             : 6
% 0.22/0.47  #    Non-unit-clauses                  : 76
% 0.22/0.47  # Current number of unprocessed clauses: 4969
% 0.22/0.47  # ...number of literals in the above   : 12114
% 0.22/0.47  # Current number of archived formulas  : 0
% 0.22/0.47  # Current number of archived clauses   : 168
% 0.22/0.47  # Clause-clause subsumption calls (NU) : 5155
% 0.22/0.47  # Rec. Clause-clause subsumption calls : 3318
% 0.22/0.47  # Non-unit clause-clause subsumptions  : 392
% 0.22/0.47  # Unit Clause-clause subsumption calls : 377
% 0.22/0.47  # Rewrite failures with RHS unbound    : 0
% 0.22/0.47  # BW rewrite match attempts            : 249
% 0.22/0.47  # BW rewrite match successes           : 154
% 0.22/0.47  # Condensation attempts                : 0
% 0.22/0.47  # Condensation successes               : 0
% 0.22/0.47  # Termbank termtop insertions          : 79624
% 0.22/0.47  
% 0.22/0.47  # -------------------------------------------------
% 0.22/0.47  # User time                : 0.113 s
% 0.22/0.47  # System time              : 0.005 s
% 0.22/0.47  # Total time               : 0.118 s
% 0.22/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
