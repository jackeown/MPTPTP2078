%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:59 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 792 expanded)
%              Number of clauses        :   42 ( 353 expanded)
%              Number of leaves         :   12 ( 212 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 992 expanded)
%              Number of equality atoms :   61 ( 806 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(c_0_12,plain,(
    ! [X15] : k3_xboole_0(X15,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_13,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_17,plain,(
    ! [X14] : k2_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_18,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

fof(c_0_20,plain,(
    ! [X27,X28] : k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28)) = X27 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_21,plain,(
    ! [X22,X23,X24] : k4_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(k4_xboole_0(X22,X24),k4_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_27,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k4_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_28,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_35,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = k2_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_25])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_36]),c_0_37])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_25]),c_0_37]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_39])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_41]),c_0_24])).

cnf(c_0_47,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_43]),c_0_32])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_48])])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(X1,esk4_0)) = k4_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1)) = k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_53])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)) = k4_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = k2_xboole_0(X2,X1)
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_55]),c_0_60])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_25]),c_0_37]),c_0_25]),c_0_63]),c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:19:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.50/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.50/0.70  # and selection function SelectLargestOrientable.
% 0.50/0.70  #
% 0.50/0.70  # Preprocessing time       : 0.026 s
% 0.50/0.70  # Presaturation interreduction done
% 0.50/0.70  
% 0.50/0.70  # Proof found!
% 0.50/0.70  # SZS status Theorem
% 0.50/0.70  # SZS output start CNFRefutation
% 0.50/0.70  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.50/0.70  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.50/0.70  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.50/0.70  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.50/0.70  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.50/0.70  fof(t71_xboole_1, conjecture, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 0.50/0.70  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.50/0.70  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.50/0.70  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.50/0.70  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.50/0.70  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.50/0.70  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.50/0.70  fof(c_0_12, plain, ![X15]:k3_xboole_0(X15,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.50/0.70  fof(c_0_13, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.50/0.70  cnf(c_0_14, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.50/0.70  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.70  fof(c_0_16, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.50/0.70  fof(c_0_17, plain, ![X14]:k2_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.50/0.70  fof(c_0_18, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.50/0.70  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3)), inference(assume_negation,[status(cth)],[t71_xboole_1])).
% 0.50/0.70  fof(c_0_20, plain, ![X27, X28]:k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))=X27, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.50/0.70  fof(c_0_21, plain, ![X22, X23, X24]:k4_xboole_0(k2_xboole_0(X22,X23),X24)=k2_xboole_0(k4_xboole_0(X22,X24),k4_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.50/0.70  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.50/0.70  cnf(c_0_23, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.70  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.70  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.70  fof(c_0_26, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)&r1_xboole_0(esk3_0,esk4_0))&r1_xboole_0(esk5_0,esk4_0))&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.50/0.70  fof(c_0_27, plain, ![X19, X20, X21]:k4_xboole_0(k4_xboole_0(X19,X20),X21)=k4_xboole_0(X19,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.50/0.70  fof(c_0_28, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.50/0.70  cnf(c_0_29, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.70  cnf(c_0_30, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.70  cnf(c_0_31, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.50/0.70  cnf(c_0_32, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.50/0.70  cnf(c_0_33, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.70  fof(c_0_34, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.50/0.70  fof(c_0_35, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.50/0.70  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.50/0.70  cnf(c_0_37, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.50/0.70  cnf(c_0_38, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_29, c_0_15])).
% 0.50/0.70  cnf(c_0_39, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.50/0.70  cnf(c_0_40, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=k2_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_25])).
% 0.50/0.70  cnf(c_0_41, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.50/0.70  cnf(c_0_42, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.50/0.70  cnf(c_0_43, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_36]), c_0_37])).
% 0.50/0.70  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_25]), c_0_37]), c_0_25])).
% 0.50/0.70  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_39])).
% 0.50/0.70  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_41]), c_0_24])).
% 0.50/0.70  cnf(c_0_47, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_42, c_0_15])).
% 0.50/0.70  cnf(c_0_48, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.70  cnf(c_0_49, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k4_xboole_0(X2,k2_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_43]), c_0_32])).
% 0.50/0.70  cnf(c_0_50, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0))=esk5_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.50/0.70  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_46])).
% 0.50/0.70  cnf(c_0_52, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_48])])).
% 0.50/0.70  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.50/0.70  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(X1,esk4_0))=k4_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_49])).
% 0.50/0.70  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.50/0.70  cnf(c_0_56, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1))=k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_53])).
% 0.50/0.70  cnf(c_0_57, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 0.50/0.70  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))=k4_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_55])).
% 0.50/0.70  cnf(c_0_59, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_24])).
% 0.50/0.70  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.70  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=k2_xboole_0(X2,X1)|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_37, c_0_57])).
% 0.50/0.70  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_55])).
% 0.50/0.70  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk3_0,esk5_0)=esk3_0), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.50/0.70  cnf(c_0_64, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.70  cnf(c_0_65, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_55]), c_0_60])])).
% 0.50/0.70  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_25]), c_0_37]), c_0_25]), c_0_63]), c_0_64]), c_0_65]), ['proof']).
% 0.50/0.70  # SZS output end CNFRefutation
% 0.50/0.70  # Proof object total steps             : 67
% 0.50/0.70  # Proof object clause steps            : 42
% 0.50/0.70  # Proof object formula steps           : 25
% 0.50/0.70  # Proof object conjectures             : 20
% 0.50/0.70  # Proof object clause conjectures      : 17
% 0.50/0.70  # Proof object formula conjectures     : 3
% 0.50/0.70  # Proof object initial clauses used    : 15
% 0.50/0.70  # Proof object initial formulas used   : 12
% 0.50/0.70  # Proof object generating inferences   : 21
% 0.50/0.70  # Proof object simplifying inferences  : 29
% 0.50/0.70  # Training examples: 0 positive, 0 negative
% 0.50/0.70  # Parsed axioms                        : 12
% 0.50/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.70  # Initial clauses                      : 16
% 0.50/0.70  # Removed in clause preprocessing      : 1
% 0.50/0.70  # Initial clauses in saturation        : 15
% 0.50/0.70  # Processed clauses                    : 3829
% 0.50/0.70  # ...of these trivial                  : 253
% 0.50/0.70  # ...subsumed                          : 3090
% 0.50/0.70  # ...remaining for further processing  : 486
% 0.50/0.70  # Other redundant clauses eliminated   : 11
% 0.50/0.70  # Clauses deleted for lack of memory   : 0
% 0.50/0.70  # Backward-subsumed                    : 35
% 0.50/0.70  # Backward-rewritten                   : 146
% 0.50/0.70  # Generated clauses                    : 42034
% 0.50/0.70  # ...of the previous two non-trivial   : 27595
% 0.50/0.70  # Contextual simplify-reflections      : 2
% 0.50/0.70  # Paramodulations                      : 42012
% 0.50/0.70  # Factorizations                       : 10
% 0.50/0.70  # Equation resolutions                 : 11
% 0.50/0.70  # Propositional unsat checks           : 0
% 0.50/0.70  #    Propositional check models        : 0
% 0.50/0.70  #    Propositional check unsatisfiable : 0
% 0.50/0.70  #    Propositional clauses             : 0
% 0.50/0.70  #    Propositional clauses after purity: 0
% 0.50/0.70  #    Propositional unsat core size     : 0
% 0.50/0.70  #    Propositional preprocessing time  : 0.000
% 0.50/0.70  #    Propositional encoding time       : 0.000
% 0.50/0.70  #    Propositional solver time         : 0.000
% 0.50/0.70  #    Success case prop preproc time    : 0.000
% 0.50/0.70  #    Success case prop encoding time   : 0.000
% 0.50/0.70  #    Success case prop solver time     : 0.000
% 0.50/0.70  # Current number of processed clauses  : 289
% 0.50/0.70  #    Positive orientable unit clauses  : 104
% 0.50/0.70  #    Positive unorientable unit clauses: 1
% 0.50/0.70  #    Negative unit clauses             : 24
% 0.50/0.70  #    Non-unit-clauses                  : 160
% 0.50/0.70  # Current number of unprocessed clauses: 23415
% 0.50/0.70  # ...number of literals in the above   : 68170
% 0.50/0.70  # Current number of archived formulas  : 0
% 0.50/0.70  # Current number of archived clauses   : 198
% 0.50/0.70  # Clause-clause subsumption calls (NU) : 26602
% 0.50/0.70  # Rec. Clause-clause subsumption calls : 20389
% 0.50/0.70  # Non-unit clause-clause subsumptions  : 1980
% 0.50/0.70  # Unit Clause-clause subsumption calls : 708
% 0.50/0.70  # Rewrite failures with RHS unbound    : 0
% 0.50/0.70  # BW rewrite match attempts            : 250
% 0.50/0.70  # BW rewrite match successes           : 78
% 0.50/0.70  # Condensation attempts                : 0
% 0.50/0.70  # Condensation successes               : 0
% 0.50/0.70  # Termbank termtop insertions          : 587729
% 0.50/0.71  
% 0.50/0.71  # -------------------------------------------------
% 0.50/0.71  # User time                : 0.356 s
% 0.50/0.71  # System time              : 0.015 s
% 0.50/0.71  # Total time               : 0.371 s
% 0.50/0.71  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
