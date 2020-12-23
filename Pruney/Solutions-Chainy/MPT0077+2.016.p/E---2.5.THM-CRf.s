%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:55 EST 2020

% Result     : Theorem 21.27s
% Output     : CNFRefutation 21.27s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 175 expanded)
%              Number of clauses        :   36 (  80 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 397 expanded)
%              Number of equality atoms :   35 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

fof(c_0_13,plain,(
    ! [X18,X19] : k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_14,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_xboole_0(X21,X22)
      | r1_xboole_0(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_16,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_18,negated_conjecture,
    ( ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk3_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_34,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X11] : k3_xboole_0(X11,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)
    | r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0)
    | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k4_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_20])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_49])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_44]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_55]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 21.27/21.46  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 21.27/21.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 21.27/21.46  #
% 21.27/21.46  # Preprocessing time       : 0.027 s
% 21.27/21.46  # Presaturation interreduction done
% 21.27/21.46  
% 21.27/21.46  # Proof found!
% 21.27/21.46  # SZS status Theorem
% 21.27/21.46  # SZS output start CNFRefutation
% 21.27/21.46  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 21.27/21.46  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 21.27/21.46  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.27/21.46  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 21.27/21.46  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 21.27/21.46  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 21.27/21.46  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 21.27/21.46  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 21.27/21.46  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 21.27/21.46  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 21.27/21.46  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 21.27/21.46  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 21.27/21.46  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 21.27/21.46  fof(c_0_13, plain, ![X18, X19]:k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 21.27/21.46  fof(c_0_14, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 21.27/21.46  fof(c_0_15, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_xboole_0(X21,X22)|r1_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 21.27/21.46  fof(c_0_16, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 21.27/21.46  fof(c_0_17, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 21.27/21.46  fof(c_0_18, negated_conjecture, ((((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk2_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk3_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 21.27/21.46  cnf(c_0_19, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 21.27/21.46  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 21.27/21.46  fof(c_0_21, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 21.27/21.46  fof(c_0_22, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 21.27/21.46  cnf(c_0_23, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 21.27/21.46  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 21.27/21.46  cnf(c_0_25, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 21.27/21.46  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 21.27/21.46  cnf(c_0_27, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 21.27/21.46  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 21.27/21.46  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 21.27/21.46  fof(c_0_30, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 21.27/21.46  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 21.27/21.46  cnf(c_0_32, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)|r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 21.27/21.46  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 21.27/21.46  fof(c_0_34, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 21.27/21.46  cnf(c_0_35, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 21.27/21.46  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_20])).
% 21.27/21.46  cnf(c_0_37, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 21.27/21.46  fof(c_0_38, plain, ![X11]:k3_xboole_0(X11,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 21.27/21.46  cnf(c_0_39, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25])).
% 21.27/21.46  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 21.27/21.46  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)|r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 21.27/21.46  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 21.27/21.46  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 21.27/21.46  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 21.27/21.46  cnf(c_0_45, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 21.27/21.46  fof(c_0_46, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 21.27/21.46  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 21.27/21.46  cnf(c_0_48, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_39])).
% 21.27/21.46  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_25])).
% 21.27/21.46  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_20])).
% 21.27/21.46  cnf(c_0_51, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k4_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 21.27/21.46  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_20])).
% 21.27/21.46  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 21.27/21.46  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 21.27/21.46  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_49])).
% 21.27/21.46  cnf(c_0_56, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 21.27/21.46  cnf(c_0_57, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 21.27/21.46  cnf(c_0_58, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 21.27/21.46  cnf(c_0_59, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_44]), c_0_57])])).
% 21.27/21.46  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_55]), c_0_48])]), ['proof']).
% 21.27/21.46  # SZS output end CNFRefutation
% 21.27/21.46  # Proof object total steps             : 61
% 21.27/21.46  # Proof object clause steps            : 36
% 21.27/21.46  # Proof object formula steps           : 25
% 21.27/21.46  # Proof object conjectures             : 15
% 21.27/21.46  # Proof object clause conjectures      : 12
% 21.27/21.46  # Proof object formula conjectures     : 3
% 21.27/21.46  # Proof object initial clauses used    : 15
% 21.27/21.46  # Proof object initial formulas used   : 12
% 21.27/21.46  # Proof object generating inferences   : 13
% 21.27/21.46  # Proof object simplifying inferences  : 18
% 21.27/21.46  # Training examples: 0 positive, 0 negative
% 21.27/21.46  # Parsed axioms                        : 12
% 21.27/21.46  # Removed by relevancy pruning/SinE    : 0
% 21.27/21.46  # Initial clauses                      : 18
% 21.27/21.46  # Removed in clause preprocessing      : 4
% 21.27/21.46  # Initial clauses in saturation        : 14
% 21.27/21.46  # Processed clauses                    : 78678
% 21.27/21.46  # ...of these trivial                  : 476
% 21.27/21.46  # ...subsumed                          : 74483
% 21.27/21.46  # ...remaining for further processing  : 3719
% 21.27/21.46  # Other redundant clauses eliminated   : 0
% 21.27/21.46  # Clauses deleted for lack of memory   : 0
% 21.27/21.46  # Backward-subsumed                    : 216
% 21.27/21.46  # Backward-rewritten                   : 34
% 21.27/21.46  # Generated clauses                    : 2625053
% 21.27/21.46  # ...of the previous two non-trivial   : 2354369
% 21.27/21.46  # Contextual simplify-reflections      : 144
% 21.27/21.46  # Paramodulations                      : 2625043
% 21.27/21.46  # Factorizations                       : 0
% 21.27/21.46  # Equation resolutions                 : 10
% 21.27/21.46  # Propositional unsat checks           : 0
% 21.27/21.46  #    Propositional check models        : 0
% 21.27/21.46  #    Propositional check unsatisfiable : 0
% 21.27/21.46  #    Propositional clauses             : 0
% 21.27/21.46  #    Propositional clauses after purity: 0
% 21.27/21.46  #    Propositional unsat core size     : 0
% 21.27/21.46  #    Propositional preprocessing time  : 0.000
% 21.27/21.46  #    Propositional encoding time       : 0.000
% 21.27/21.46  #    Propositional solver time         : 0.000
% 21.27/21.46  #    Success case prop preproc time    : 0.000
% 21.27/21.46  #    Success case prop encoding time   : 0.000
% 21.27/21.46  #    Success case prop solver time     : 0.000
% 21.27/21.46  # Current number of processed clauses  : 3455
% 21.27/21.46  #    Positive orientable unit clauses  : 196
% 21.27/21.46  #    Positive unorientable unit clauses: 9
% 21.27/21.46  #    Negative unit clauses             : 4
% 21.27/21.46  #    Non-unit-clauses                  : 3246
% 21.27/21.46  # Current number of unprocessed clauses: 2273249
% 21.27/21.46  # ...number of literals in the above   : 6858192
% 21.27/21.46  # Current number of archived formulas  : 0
% 21.27/21.46  # Current number of archived clauses   : 265
% 21.27/21.46  # Clause-clause subsumption calls (NU) : 1524948
% 21.27/21.46  # Rec. Clause-clause subsumption calls : 1470029
% 21.27/21.46  # Non-unit clause-clause subsumptions  : 72421
% 21.27/21.46  # Unit Clause-clause subsumption calls : 1843
% 21.27/21.46  # Rewrite failures with RHS unbound    : 0
% 21.27/21.46  # BW rewrite match attempts            : 6998
% 21.27/21.46  # BW rewrite match successes           : 563
% 21.27/21.46  # Condensation attempts                : 0
% 21.27/21.46  # Condensation successes               : 0
% 21.27/21.46  # Termbank termtop insertions          : 46164450
% 21.37/21.55  
% 21.37/21.55  # -------------------------------------------------
% 21.37/21.55  # User time                : 20.281 s
% 21.37/21.55  # System time              : 0.927 s
% 21.37/21.55  # Total time               : 21.208 s
% 21.37/21.55  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
