%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 195 expanded)
%              Number of clauses        :   19 (  86 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 291 expanded)
%              Number of equality atoms :   41 ( 190 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t51_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(t97_mcart_1,conjecture,(
    ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( k3_xboole_0(X21,k1_tarski(X22)) != k1_tarski(X22)
      | r2_hidden(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).

cnf(c_0_17,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_13])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t97_mcart_1])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_18])])).

fof(c_0_24,negated_conjecture,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk2_0,esk3_0,esk4_0)))) != k1_tarski(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_25,plain,(
    ! [X25,X26,X27] : k3_mcart_1(X25,X26,X27) = k4_tarski(k4_tarski(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_26,plain,(
    ! [X23,X24] :
      ( ( k1_relat_1(k2_zfmisc_1(X23,X24)) = X23
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X23,X24)) = X24
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

fof(c_0_27,plain,(
    ! [X19,X20] : k2_zfmisc_1(k1_tarski(X19),k1_tarski(X20)) = k1_tarski(k4_tarski(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X2))) != k1_tarski(X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk2_0,esk3_0,esk4_0)))) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_18]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0)))) != k1_tarski(esk2_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X1,X2))) = k1_tarski(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S027I
% 0.20/0.38  # and selection function PSelectOptimalRestrNDepth2.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.037 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.38  fof(t51_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 0.20/0.38  fof(t97_mcart_1, conjecture, ![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 0.20/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.38  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.20/0.38  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.20/0.38  fof(c_0_9, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.38  cnf(c_0_12, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_14, plain, ![X14]:k4_xboole_0(k1_xboole_0,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.38  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_16, plain, ![X21, X22]:(k3_xboole_0(X21,k1_tarski(X22))!=k1_tarski(X22)|r2_hidden(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).
% 0.20/0.38  cnf(c_0_17, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_18, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_13])).
% 0.20/0.38  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t97_mcart_1])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.20/0.39  cnf(c_0_23, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_18]), c_0_18])])).
% 0.20/0.39  fof(c_0_24, negated_conjecture, k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk2_0,esk3_0,esk4_0))))!=k1_tarski(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.39  fof(c_0_25, plain, ![X25, X26, X27]:k3_mcart_1(X25,X26,X27)=k4_tarski(k4_tarski(X25,X26),X27), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.39  fof(c_0_26, plain, ![X23, X24]:((k1_relat_1(k2_zfmisc_1(X23,X24))=X23|(X23=k1_xboole_0|X24=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X23,X24))=X24|(X23=k1_xboole_0|X24=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.20/0.39  fof(c_0_27, plain, ![X19, X20]:k2_zfmisc_1(k1_tarski(X19),k1_tarski(X20))=k1_tarski(k4_tarski(X19,X20)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.20/0.39  cnf(c_0_28, plain, (r2_hidden(X2,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X2)))!=k1_tarski(X2)), inference(rw,[status(thm)],[c_0_21, c_0_13])).
% 0.20/0.39  cnf(c_0_29, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk2_0,esk3_0,esk4_0))))!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_31, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_32, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_33, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_34, plain, (k1_tarski(X1)!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_18]), c_0_29])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (k1_relat_1(k1_relat_1(k1_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0))))!=k1_tarski(esk2_0)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_36, plain, (k1_relat_1(k1_tarski(k4_tarski(X1,X2)))=k1_tarski(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_34])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 38
% 0.20/0.39  # Proof object clause steps            : 19
% 0.20/0.39  # Proof object formula steps           : 19
% 0.20/0.39  # Proof object conjectures             : 6
% 0.20/0.39  # Proof object clause conjectures      : 3
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 9
% 0.20/0.39  # Proof object initial formulas used   : 9
% 0.20/0.39  # Proof object generating inferences   : 4
% 0.20/0.39  # Proof object simplifying inferences  : 16
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 11
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 15
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 13
% 0.20/0.39  # Processed clauses                    : 36
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 2
% 0.20/0.39  # ...remaining for further processing  : 33
% 0.20/0.39  # Other redundant clauses eliminated   : 1
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 2
% 0.20/0.39  # Generated clauses                    : 14
% 0.20/0.39  # ...of the previous two non-trivial   : 14
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 13
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 1
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 17
% 0.20/0.39  #    Positive orientable unit clauses  : 5
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 9
% 0.20/0.39  # Current number of unprocessed clauses: 4
% 0.20/0.39  # ...number of literals in the above   : 10
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 17
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 8
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 4
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.39  # Unit Clause-clause subsumption calls : 4
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1142
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.038 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.044 s
% 0.20/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
