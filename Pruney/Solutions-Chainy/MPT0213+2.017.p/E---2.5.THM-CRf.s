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
% DateTime   : Thu Dec  3 10:36:56 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 260 expanded)
%              Number of clauses        :   21 ( 135 expanded)
%              Number of leaves         :    5 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 (1150 expanded)
%              Number of equality atoms :   24 ( 284 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t2_zfmisc_1,conjecture,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( r2_hidden(X16,esk2_3(X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | X15 != k3_tarski(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_tarski(X14) )
      & ( ~ r2_hidden(X18,X19)
        | ~ r2_hidden(X19,X14)
        | r2_hidden(X18,X15)
        | X15 != k3_tarski(X14) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X21)
        | ~ r2_hidden(esk3_2(X20,X21),X23)
        | ~ r2_hidden(X23,X20)
        | X21 = k3_tarski(X20) )
      & ( r2_hidden(esk3_2(X20,X21),esk4_2(X20,X21))
        | r2_hidden(esk3_2(X20,X21),X21)
        | X21 = k3_tarski(X20) )
      & ( r2_hidden(esk4_2(X20,X21),X20)
        | r2_hidden(esk3_2(X20,X21),X21)
        | X21 = k3_tarski(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_11,plain,(
    ! [X12,X13] : r1_xboole_0(k4_xboole_0(X12,X13),X13) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_12,plain,(
    ! [X11] : k4_xboole_0(k1_xboole_0,X11) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X3)
    | ~ r2_hidden(X2,k3_tarski(X1))
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ r2_hidden(esk4_2(X2,X1),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_10])).

cnf(c_0_15,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k3_tarski(X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_18,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(X2)))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_9])).

cnf(c_0_21,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( k3_tarski(k3_tarski(X1)) = k3_tarski(k1_xboole_0)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_23]),c_0_19])])).

fof(c_0_25,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t2_zfmisc_1])).

cnf(c_0_26,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk4_2(X2,X1),X2)
    | ~ r2_hidden(esk3_2(X2,X1),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_10])).

cnf(c_0_27,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk3_2(k3_tarski(k1_xboole_0),X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_10]),c_0_23])).

fof(c_0_28,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | ~ r1_xboole_0(X1,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_19]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.21/0.45  # and selection function SelectComplexExceptRRHorn.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.039 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.21/0.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.45  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.21/0.45  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.21/0.45  fof(t2_zfmisc_1, conjecture, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.21/0.45  fof(c_0_5, plain, ![X14, X15, X16, X18, X19, X20, X21, X23]:((((r2_hidden(X16,esk2_3(X14,X15,X16))|~r2_hidden(X16,X15)|X15!=k3_tarski(X14))&(r2_hidden(esk2_3(X14,X15,X16),X14)|~r2_hidden(X16,X15)|X15!=k3_tarski(X14)))&(~r2_hidden(X18,X19)|~r2_hidden(X19,X14)|r2_hidden(X18,X15)|X15!=k3_tarski(X14)))&((~r2_hidden(esk3_2(X20,X21),X21)|(~r2_hidden(esk3_2(X20,X21),X23)|~r2_hidden(X23,X20))|X21=k3_tarski(X20))&((r2_hidden(esk3_2(X20,X21),esk4_2(X20,X21))|r2_hidden(esk3_2(X20,X21),X21)|X21=k3_tarski(X20))&(r2_hidden(esk4_2(X20,X21),X20)|r2_hidden(esk3_2(X20,X21),X21)|X21=k3_tarski(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.21/0.45  fof(c_0_6, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.45  cnf(c_0_7, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.45  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.45  cnf(c_0_9, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_7])).
% 0.21/0.45  cnf(c_0_10, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.45  fof(c_0_11, plain, ![X12, X13]:r1_xboole_0(k4_xboole_0(X12,X13),X13), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.21/0.45  fof(c_0_12, plain, ![X11]:k4_xboole_0(k1_xboole_0,X11)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.21/0.45  cnf(c_0_13, plain, (~r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X3)|~r2_hidden(X2,k3_tarski(X1))|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.21/0.45  cnf(c_0_14, plain, (X1=k3_tarski(X2)|r2_hidden(esk3_2(X2,X1),X1)|~r2_hidden(esk4_2(X2,X1),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_8, c_0_10])).
% 0.21/0.45  cnf(c_0_15, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.45  cnf(c_0_16, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.45  cnf(c_0_17, plain, (~r2_hidden(X1,k3_tarski(X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_13, c_0_9])).
% 0.21/0.45  cnf(c_0_18, plain, (X1=k3_tarski(X2)|r2_hidden(esk3_2(X2,X1),X1)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_14, c_0_10])).
% 0.21/0.45  cnf(c_0_19, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.45  cnf(c_0_20, plain, (~r2_hidden(X1,k3_tarski(k3_tarski(X2)))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_17, c_0_9])).
% 0.21/0.45  cnf(c_0_21, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.45  cnf(c_0_22, plain, (k3_tarski(k3_tarski(X1))=k3_tarski(k1_xboole_0)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.45  cnf(c_0_23, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.21/0.45  cnf(c_0_24, plain, (~r2_hidden(X1,k3_tarski(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_23]), c_0_19])])).
% 0.21/0.45  fof(c_0_25, negated_conjecture, ~(k3_tarski(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t2_zfmisc_1])).
% 0.21/0.45  cnf(c_0_26, plain, (X1=k3_tarski(X2)|r2_hidden(esk4_2(X2,X1),X2)|~r2_hidden(esk3_2(X2,X1),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_8, c_0_10])).
% 0.21/0.45  cnf(c_0_27, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk3_2(k3_tarski(k1_xboole_0),X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_10]), c_0_23])).
% 0.21/0.45  fof(c_0_28, negated_conjecture, k3_tarski(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_25])).
% 0.21/0.45  cnf(c_0_29, plain, (X1=k3_tarski(k1_xboole_0)|~r1_xboole_0(X1,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23])]), c_0_24])).
% 0.21/0.45  cnf(c_0_30, negated_conjecture, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.45  cnf(c_0_31, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_19]), c_0_30]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 32
% 0.21/0.45  # Proof object clause steps            : 21
% 0.21/0.45  # Proof object formula steps           : 11
% 0.21/0.45  # Proof object conjectures             : 4
% 0.21/0.45  # Proof object clause conjectures      : 1
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 6
% 0.21/0.45  # Proof object initial formulas used   : 5
% 0.21/0.45  # Proof object generating inferences   : 14
% 0.21/0.45  # Proof object simplifying inferences  : 8
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 5
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 12
% 0.21/0.45  # Removed in clause preprocessing      : 0
% 0.21/0.45  # Initial clauses in saturation        : 12
% 0.21/0.45  # Processed clauses                    : 441
% 0.21/0.45  # ...of these trivial                  : 26
% 0.21/0.45  # ...subsumed                          : 228
% 0.21/0.45  # ...remaining for further processing  : 187
% 0.21/0.45  # Other redundant clauses eliminated   : 3
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 0
% 0.21/0.45  # Backward-rewritten                   : 42
% 0.21/0.45  # Generated clauses                    : 1948
% 0.21/0.45  # ...of the previous two non-trivial   : 1874
% 0.21/0.45  # Contextual simplify-reflections      : 1
% 0.21/0.45  # Paramodulations                      : 1945
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 3
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 130
% 0.21/0.45  #    Positive orientable unit clauses  : 8
% 0.21/0.45  #    Positive unorientable unit clauses: 0
% 0.21/0.45  #    Negative unit clauses             : 2
% 0.21/0.45  #    Non-unit-clauses                  : 120
% 0.21/0.45  # Current number of unprocessed clauses: 1439
% 0.21/0.45  # ...number of literals in the above   : 4876
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 54
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 2564
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 2170
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 97
% 0.21/0.45  # Unit Clause-clause subsumption calls : 23
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 3
% 0.21/0.45  # BW rewrite match successes           : 3
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 51765
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.103 s
% 0.21/0.45  # System time              : 0.005 s
% 0.21/0.45  # Total time               : 0.108 s
% 0.21/0.45  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
