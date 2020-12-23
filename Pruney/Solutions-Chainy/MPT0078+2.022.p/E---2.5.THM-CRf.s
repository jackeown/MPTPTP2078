%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 629 expanded)
%              Number of clauses        :   44 ( 275 expanded)
%              Number of leaves         :    9 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :   94 ( 937 expanded)
%              Number of equality atoms :   47 ( 616 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

fof(c_0_10,plain,(
    ! [X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),X18) = k4_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X14] : k2_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_14,plain,(
    ! [X21,X22] : k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22)) = X21 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_15,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X16,X15)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = k2_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18]),c_0_18])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_29])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_18]),c_0_30]),c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_36]),c_0_39])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_17]),c_0_30])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_45,plain,
    ( X1 = X2
    | r2_hidden(esk2_1(X2),X2)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_36])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_18])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_29]),c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_42])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_20])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_46]),c_0_47])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_49])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_50]),c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_59]),c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.20/0.53  # and selection function SelectLargestOrientable.
% 0.20/0.53  #
% 0.20/0.53  # Preprocessing time       : 0.026 s
% 0.20/0.53  # Presaturation interreduction done
% 0.20/0.53  
% 0.20/0.53  # Proof found!
% 0.20/0.53  # SZS status Theorem
% 0.20/0.53  # SZS output start CNFRefutation
% 0.20/0.53  fof(t71_xboole_1, conjecture, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 0.20/0.53  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.53  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.53  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.53  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.53  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.53  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.53  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.53  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.53  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3)), inference(assume_negation,[status(cth)],[t71_xboole_1])).
% 0.20/0.53  fof(c_0_10, plain, ![X17, X18]:k4_xboole_0(k2_xboole_0(X17,X18),X18)=k4_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.53  fof(c_0_11, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.53  fof(c_0_12, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)&r1_xboole_0(esk3_0,esk4_0))&r1_xboole_0(esk5_0,esk4_0))&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.53  fof(c_0_13, plain, ![X14]:k2_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.53  fof(c_0_14, plain, ![X21, X22]:k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))=X21, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.53  fof(c_0_15, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.53  fof(c_0_16, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.53  cnf(c_0_17, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.53  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.53  cnf(c_0_19, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.53  cnf(c_0_20, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.53  fof(c_0_21, plain, ![X15, X16]:k2_xboole_0(X15,k4_xboole_0(X16,X15))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.53  cnf(c_0_22, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.53  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.53  cnf(c_0_24, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.53  cnf(c_0_25, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.53  cnf(c_0_26, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=k2_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18]), c_0_18])).
% 0.20/0.53  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.53  fof(c_0_28, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.53  cnf(c_0_29, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.20/0.53  cnf(c_0_30, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.53  cnf(c_0_31, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.53  cnf(c_0_32, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.20/0.53  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_25])).
% 0.20/0.53  cnf(c_0_34, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.53  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_27, c_0_23])).
% 0.20/0.53  cnf(c_0_36, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.53  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_29])).
% 0.20/0.53  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_18]), c_0_30]), c_0_18])).
% 0.20/0.53  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.20/0.53  cnf(c_0_40, plain, (r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.20/0.53  cnf(c_0_41, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.20/0.53  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_36]), c_0_39])).
% 0.20/0.53  cnf(c_0_43, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_17]), c_0_30])).
% 0.20/0.53  cnf(c_0_44, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_42])).
% 0.20/0.53  cnf(c_0_45, plain, (X1=X2|r2_hidden(esk2_1(X2),X2)|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_36, c_0_36])).
% 0.20/0.53  cnf(c_0_46, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_18])).
% 0.20/0.53  cnf(c_0_47, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_29]), c_0_41])).
% 0.20/0.53  cnf(c_0_48, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_42])).
% 0.20/0.53  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_20])).
% 0.20/0.53  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_46]), c_0_47])).
% 0.20/0.53  cnf(c_0_51, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_48])).
% 0.20/0.53  cnf(c_0_52, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.53  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0))=esk5_0), inference(spm,[status(thm)],[c_0_38, c_0_33])).
% 0.20/0.53  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_49])).
% 0.20/0.53  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_50]), c_0_37])).
% 0.20/0.53  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.53  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_39])).
% 0.20/0.53  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.53  cnf(c_0_59, negated_conjecture, (k2_xboole_0(esk3_0,esk5_0)=esk3_0), inference(spm,[status(thm)],[c_0_38, c_0_57])).
% 0.20/0.53  cnf(c_0_60, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.53  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_58, c_0_57])).
% 0.20/0.53  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_59]), c_0_60]), c_0_61]), ['proof']).
% 0.20/0.53  # SZS output end CNFRefutation
% 0.20/0.53  # Proof object total steps             : 63
% 0.20/0.53  # Proof object clause steps            : 44
% 0.20/0.53  # Proof object formula steps           : 19
% 0.20/0.53  # Proof object conjectures             : 18
% 0.20/0.53  # Proof object clause conjectures      : 15
% 0.20/0.53  # Proof object formula conjectures     : 3
% 0.20/0.53  # Proof object initial clauses used    : 13
% 0.20/0.53  # Proof object initial formulas used   : 9
% 0.20/0.53  # Proof object generating inferences   : 25
% 0.20/0.53  # Proof object simplifying inferences  : 26
% 0.20/0.53  # Training examples: 0 positive, 0 negative
% 0.20/0.53  # Parsed axioms                        : 9
% 0.20/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.53  # Initial clauses                      : 13
% 0.20/0.53  # Removed in clause preprocessing      : 1
% 0.20/0.53  # Initial clauses in saturation        : 12
% 0.20/0.53  # Processed clauses                    : 2410
% 0.20/0.53  # ...of these trivial                  : 193
% 0.20/0.53  # ...subsumed                          : 1818
% 0.20/0.53  # ...remaining for further processing  : 399
% 0.20/0.53  # Other redundant clauses eliminated   : 13
% 0.20/0.53  # Clauses deleted for lack of memory   : 0
% 0.20/0.53  # Backward-subsumed                    : 19
% 0.20/0.53  # Backward-rewritten                   : 119
% 0.20/0.53  # Generated clauses                    : 16325
% 0.20/0.53  # ...of the previous two non-trivial   : 9858
% 0.20/0.53  # Contextual simplify-reflections      : 7
% 0.20/0.53  # Paramodulations                      : 16308
% 0.20/0.53  # Factorizations                       : 4
% 0.20/0.53  # Equation resolutions                 : 13
% 0.20/0.53  # Propositional unsat checks           : 0
% 0.20/0.53  #    Propositional check models        : 0
% 0.20/0.53  #    Propositional check unsatisfiable : 0
% 0.20/0.53  #    Propositional clauses             : 0
% 0.20/0.53  #    Propositional clauses after purity: 0
% 0.20/0.53  #    Propositional unsat core size     : 0
% 0.20/0.53  #    Propositional preprocessing time  : 0.000
% 0.20/0.53  #    Propositional encoding time       : 0.000
% 0.20/0.53  #    Propositional solver time         : 0.000
% 0.20/0.53  #    Success case prop preproc time    : 0.000
% 0.20/0.53  #    Success case prop encoding time   : 0.000
% 0.20/0.53  #    Success case prop solver time     : 0.000
% 0.20/0.53  # Current number of processed clauses  : 249
% 0.20/0.53  #    Positive orientable unit clauses  : 44
% 0.20/0.53  #    Positive unorientable unit clauses: 1
% 0.20/0.53  #    Negative unit clauses             : 14
% 0.20/0.53  #    Non-unit-clauses                  : 190
% 0.20/0.53  # Current number of unprocessed clauses: 6820
% 0.20/0.53  # ...number of literals in the above   : 23738
% 0.20/0.53  # Current number of archived formulas  : 0
% 0.20/0.53  # Current number of archived clauses   : 151
% 0.20/0.53  # Clause-clause subsumption calls (NU) : 14509
% 0.20/0.53  # Rec. Clause-clause subsumption calls : 12334
% 0.20/0.53  # Non-unit clause-clause subsumptions  : 1124
% 0.20/0.53  # Unit Clause-clause subsumption calls : 469
% 0.20/0.53  # Rewrite failures with RHS unbound    : 0
% 0.20/0.53  # BW rewrite match attempts            : 114
% 0.20/0.53  # BW rewrite match successes           : 40
% 0.20/0.53  # Condensation attempts                : 0
% 0.20/0.53  # Condensation successes               : 0
% 0.20/0.53  # Termbank termtop insertions          : 245089
% 0.20/0.53  
% 0.20/0.53  # -------------------------------------------------
% 0.20/0.53  # User time                : 0.186 s
% 0.20/0.53  # System time              : 0.004 s
% 0.20/0.53  # Total time               : 0.190 s
% 0.20/0.53  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
