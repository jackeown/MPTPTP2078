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
% DateTime   : Thu Dec  3 10:39:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 (3134 expanded)
%              Number of clauses        :   38 (1224 expanded)
%              Number of leaves         :   11 ( 931 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 (4458 expanded)
%              Number of equality atoms :   82 (4082 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_11,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_tarski(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & ( esk3_0 != k1_tarski(esk2_0)
      | esk4_0 != k1_tarski(esk2_0) )
    & ( esk3_0 != k1_xboole_0
      | esk4_0 != k1_tarski(esk2_0) )
    & ( esk3_0 != k1_tarski(esk2_0)
      | esk4_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_26,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tarski(X27,k1_tarski(X28))
        | X27 = k1_xboole_0
        | X27 = k1_tarski(X28) )
      & ( X27 != k1_xboole_0
        | r1_tarski(X27,k1_tarski(X28)) )
      & ( X27 != k1_tarski(X28)
        | r1_tarski(X27,k1_tarski(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_15]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_tarski(esk2_0)
    | esk4_0 != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_31]),c_0_31]),c_0_15]),c_0_15]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 != k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)
    | esk4_0 != k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_31]),c_0_31]),c_0_15]),c_0_15]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk3_0 != k1_tarski(esk2_0)
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk4_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk4_0 != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk3_0 != k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_31]),c_0_15]),c_0_22]),c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_43])).

fof(c_0_47,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_48,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk4_0 != k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_31]),c_0_15]),c_0_22]),c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_55,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_40,c_0_54])).

cnf(c_0_58,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_57]),c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.38  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.38  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.13/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(c_0_11, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_13, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.38  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_16, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_17, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_18, plain, ![X15, X16]:k2_tarski(X15,X16)=k2_tarski(X16,X15), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.13/0.38  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_25, negated_conjecture, (((k1_tarski(esk2_0)=k2_xboole_0(esk3_0,esk4_0)&(esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_tarski(esk2_0)))&(esk3_0!=k1_xboole_0|esk4_0!=k1_tarski(esk2_0)))&(esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.13/0.38  fof(c_0_26, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_27, plain, ![X27, X28]:((~r1_tarski(X27,k1_tarski(X28))|(X27=k1_xboole_0|X27=k1_tarski(X28)))&((X27!=k1_xboole_0|r1_tarski(X27,k1_tarski(X28)))&(X27!=k1_tarski(X28)|r1_tarski(X27,k1_tarski(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k1_tarski(esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_33, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_15]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_31]), c_0_31]), c_0_15]), c_0_15]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (esk3_0!=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)|esk4_0!=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_31]), c_0_31]), c_0_15]), c_0_15]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=esk4_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (esk3_0!=k1_tarski(esk2_0)|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=esk3_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_38])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (esk4_0=k1_xboole_0|esk4_0!=esk3_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk3_0!=k1_xboole_0|esk4_0!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (esk4_0!=k1_xboole_0|esk3_0!=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_31]), c_0_15]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_43])).
% 0.13/0.38  fof(c_0_47, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.38  fof(c_0_48, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (esk3_0!=k1_xboole_0|esk4_0!=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_31]), c_0_15]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_42])).
% 0.13/0.38  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.13/0.38  cnf(c_0_55, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_40, c_0_54])).
% 0.13/0.38  cnf(c_0_58, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_57])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_57]), c_0_58]), c_0_59]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 61
% 0.13/0.38  # Proof object clause steps            : 38
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 22
% 0.13/0.38  # Proof object clause conjectures      : 19
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 57
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 13
% 0.13/0.38  # Processed clauses                    : 73
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 13
% 0.13/0.38  # ...remaining for further processing  : 58
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 23
% 0.13/0.38  # Generated clauses                    : 113
% 0.13/0.38  # ...of the previous two non-trivial   : 82
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 110
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 19
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 8
% 0.13/0.38  # Current number of unprocessed clauses: 20
% 0.13/0.38  # ...number of literals in the above   : 43
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 42
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 36
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 33
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.13/0.38  # Unit Clause-clause subsumption calls : 8
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 37
% 0.13/0.38  # BW rewrite match successes           : 20
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2024
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
