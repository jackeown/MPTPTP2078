%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:54 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 227 expanded)
%              Number of clauses        :   39 ( 100 expanded)
%              Number of leaves         :   13 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 452 expanded)
%              Number of equality atoms :   39 ( 125 expanded)
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

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

fof(c_0_14,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_tarski(X33,X34)
      | ~ r1_xboole_0(X34,X35)
      | r1_xboole_0(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_15,plain,(
    ! [X36,X37] : r1_tarski(X36,k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_17,negated_conjecture,
    ( ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk5_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

fof(c_0_18,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_19,plain,(
    ! [X31,X32] : k2_xboole_0(k3_xboole_0(X31,X32),k4_xboole_0(X31,X32)) = X31 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_20,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_27,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),X25) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_28,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)
    | r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X26,X27,X28] : k4_xboole_0(k4_xboole_0(X26,X27),X28) = k4_xboole_0(X26,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_41,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_23])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)
    | r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_25]),c_0_38]),c_0_25])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_51,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(X18,X19) != k1_xboole_0
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | k4_xboole_0(X18,X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk5_0)
    | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_23])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_54])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(X1,k4_xboole_0(X1,X3)) != k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_53]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 3.44/3.67  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 3.44/3.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.44/3.67  #
% 3.44/3.67  # Preprocessing time       : 0.028 s
% 3.44/3.67  
% 3.44/3.67  # Proof found!
% 3.44/3.67  # SZS status Theorem
% 3.44/3.67  # SZS output start CNFRefutation
% 3.44/3.67  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.44/3.67  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.44/3.67  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.44/3.67  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.44/3.67  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.44/3.67  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.44/3.67  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.44/3.67  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.44/3.67  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.44/3.67  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.44/3.67  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.44/3.67  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.44/3.67  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.44/3.67  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 3.44/3.67  fof(c_0_14, plain, ![X33, X34, X35]:(~r1_tarski(X33,X34)|~r1_xboole_0(X34,X35)|r1_xboole_0(X33,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 3.44/3.67  fof(c_0_15, plain, ![X36, X37]:r1_tarski(X36,k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 3.44/3.67  fof(c_0_16, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 3.44/3.67  fof(c_0_17, negated_conjecture, ((((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))))&((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|r1_xboole_0(esk3_0,esk4_0))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk4_0))))&((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|r1_xboole_0(esk3_0,esk5_0))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).
% 3.44/3.67  fof(c_0_18, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 3.44/3.67  fof(c_0_19, plain, ![X31, X32]:k2_xboole_0(k3_xboole_0(X31,X32),k4_xboole_0(X31,X32))=X31, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 3.44/3.67  fof(c_0_20, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 3.44/3.67  cnf(c_0_21, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.44/3.67  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.44/3.67  cnf(c_0_23, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.44/3.67  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.44/3.67  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.44/3.67  fof(c_0_26, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 3.44/3.67  fof(c_0_27, plain, ![X24, X25]:k4_xboole_0(k2_xboole_0(X24,X25),X25)=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 3.44/3.67  fof(c_0_28, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 3.44/3.67  cnf(c_0_29, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.44/3.67  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.44/3.67  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 3.44/3.67  cnf(c_0_32, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)|r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 3.44/3.67  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 3.44/3.67  cnf(c_0_34, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.44/3.67  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.44/3.67  fof(c_0_36, plain, ![X26, X27, X28]:k4_xboole_0(k4_xboole_0(X26,X27),X28)=k4_xboole_0(X26,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 3.44/3.67  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.44/3.67  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.44/3.67  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.44/3.67  cnf(c_0_40, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 3.44/3.67  fof(c_0_41, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 3.44/3.67  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_23])).
% 3.44/3.67  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_33])).
% 3.44/3.67  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)|r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 3.44/3.67  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_30])).
% 3.44/3.67  cnf(c_0_46, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.44/3.67  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.44/3.67  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_30])).
% 3.44/3.67  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_25]), c_0_38]), c_0_25])).
% 3.44/3.67  cnf(c_0_50, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.44/3.67  fof(c_0_51, plain, ![X18, X19]:((k4_xboole_0(X18,X19)!=k1_xboole_0|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|k4_xboole_0(X18,X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 3.44/3.67  cnf(c_0_52, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.44/3.67  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_42])).
% 3.44/3.67  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_23])).
% 3.44/3.67  cnf(c_0_55, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 3.44/3.67  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_25]), c_0_49]), c_0_50]), c_0_50])).
% 3.44/3.67  cnf(c_0_57, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.44/3.67  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_22, c_0_49])).
% 3.44/3.67  cnf(c_0_59, negated_conjecture, (~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|~r1_xboole_0(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 3.44/3.67  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_54])).
% 3.44/3.67  cnf(c_0_61, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|k4_xboole_0(X1,k4_xboole_0(X1,X3))!=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 3.44/3.67  cnf(c_0_62, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 3.44/3.67  cnf(c_0_63, negated_conjecture, (~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 3.44/3.67  cnf(c_0_64, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_62])])).
% 3.44/3.67  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_53]), c_0_60])]), ['proof']).
% 3.44/3.67  # SZS output end CNFRefutation
% 3.44/3.67  # Proof object total steps             : 66
% 3.44/3.67  # Proof object clause steps            : 39
% 3.44/3.67  # Proof object formula steps           : 27
% 3.44/3.67  # Proof object conjectures             : 15
% 3.44/3.67  # Proof object clause conjectures      : 12
% 3.44/3.67  # Proof object formula conjectures     : 3
% 3.44/3.67  # Proof object initial clauses used    : 16
% 3.44/3.67  # Proof object initial formulas used   : 13
% 3.44/3.67  # Proof object generating inferences   : 17
% 3.44/3.67  # Proof object simplifying inferences  : 21
% 3.44/3.67  # Training examples: 0 positive, 0 negative
% 3.44/3.67  # Parsed axioms                        : 16
% 3.44/3.67  # Removed by relevancy pruning/SinE    : 0
% 3.44/3.67  # Initial clauses                      : 24
% 3.44/3.67  # Removed in clause preprocessing      : 4
% 3.44/3.67  # Initial clauses in saturation        : 20
% 3.44/3.67  # Processed clauses                    : 17521
% 3.44/3.67  # ...of these trivial                  : 512
% 3.44/3.67  # ...subsumed                          : 15455
% 3.44/3.67  # ...remaining for further processing  : 1554
% 3.44/3.67  # Other redundant clauses eliminated   : 0
% 3.44/3.67  # Clauses deleted for lack of memory   : 0
% 3.44/3.67  # Backward-subsumed                    : 76
% 3.44/3.67  # Backward-rewritten                   : 66
% 3.44/3.67  # Generated clauses                    : 544912
% 3.44/3.67  # ...of the previous two non-trivial   : 488781
% 3.44/3.67  # Contextual simplify-reflections      : 30
% 3.44/3.67  # Paramodulations                      : 544906
% 3.44/3.67  # Factorizations                       : 0
% 3.44/3.67  # Equation resolutions                 : 3
% 3.44/3.67  # Propositional unsat checks           : 0
% 3.44/3.67  #    Propositional check models        : 0
% 3.44/3.67  #    Propositional check unsatisfiable : 0
% 3.44/3.67  #    Propositional clauses             : 0
% 3.44/3.67  #    Propositional clauses after purity: 0
% 3.44/3.67  #    Propositional unsat core size     : 0
% 3.44/3.67  #    Propositional preprocessing time  : 0.000
% 3.44/3.67  #    Propositional encoding time       : 0.000
% 3.44/3.67  #    Propositional solver time         : 0.000
% 3.44/3.67  #    Success case prop preproc time    : 0.000
% 3.44/3.67  #    Success case prop encoding time   : 0.000
% 3.44/3.67  #    Success case prop solver time     : 0.000
% 3.44/3.67  # Current number of processed clauses  : 1411
% 3.44/3.67  #    Positive orientable unit clauses  : 162
% 3.44/3.67  #    Positive unorientable unit clauses: 3
% 3.44/3.67  #    Negative unit clauses             : 9
% 3.44/3.67  #    Non-unit-clauses                  : 1237
% 3.44/3.67  # Current number of unprocessed clauses: 470117
% 3.44/3.67  # ...number of literals in the above   : 1337291
% 3.44/3.67  # Current number of archived formulas  : 0
% 3.44/3.67  # Current number of archived clauses   : 143
% 3.44/3.67  # Clause-clause subsumption calls (NU) : 462197
% 3.44/3.67  # Rec. Clause-clause subsumption calls : 367714
% 3.44/3.67  # Non-unit clause-clause subsumptions  : 13739
% 3.44/3.67  # Unit Clause-clause subsumption calls : 1590
% 3.44/3.67  # Rewrite failures with RHS unbound    : 0
% 3.44/3.67  # BW rewrite match attempts            : 1015
% 3.44/3.67  # BW rewrite match successes           : 77
% 3.44/3.67  # Condensation attempts                : 0
% 3.44/3.67  # Condensation successes               : 0
% 3.44/3.67  # Termbank termtop insertions          : 9624240
% 3.44/3.69  
% 3.44/3.69  # -------------------------------------------------
% 3.44/3.69  # User time                : 3.131 s
% 3.44/3.69  # System time              : 0.181 s
% 3.44/3.69  # Total time               : 3.313 s
% 3.44/3.69  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
