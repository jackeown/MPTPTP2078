%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:51 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 186 expanded)
%              Number of equality atoms :   31 (  69 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,X2)
       => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t87_xboole_1])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ( ~ r1_xboole_0(X19,X20)
        | k4_xboole_0(X19,X20) = X19 )
      & ( k4_xboole_0(X19,X20) != X19
        | r1_xboole_0(X19,X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_8,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    & k2_xboole_0(k4_xboole_0(esk4_0,esk2_0),esk3_0) != k4_xboole_0(k2_xboole_0(esk4_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

fof(c_0_19,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_20,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(k4_xboole_0(X16,X18),k4_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(X1,esk2_0) = X1
    | ~ r2_hidden(esk1_3(X1,esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk4_0,esk2_0),esk3_0) != k4_xboole_0(k2_xboole_0(esk4_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0)) != k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0)) = k4_xboole_0(k2_xboole_0(esk3_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.20/0.52  # and selection function SelectComplexExceptRRHorn.
% 0.20/0.52  #
% 0.20/0.52  # Preprocessing time       : 0.026 s
% 0.20/0.52  # Presaturation interreduction done
% 0.20/0.52  
% 0.20/0.52  # Proof found!
% 0.20/0.52  # SZS status Theorem
% 0.20/0.52  # SZS output start CNFRefutation
% 0.20/0.52  fof(t87_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 0.20/0.52  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.52  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.52  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.52  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.20/0.52  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1))), inference(assume_negation,[status(cth)],[t87_xboole_1])).
% 0.20/0.52  fof(c_0_6, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.52  fof(c_0_7, plain, ![X19, X20]:((~r1_xboole_0(X19,X20)|k4_xboole_0(X19,X20)=X19)&(k4_xboole_0(X19,X20)!=X19|r1_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.52  fof(c_0_8, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)&k2_xboole_0(k4_xboole_0(esk4_0,esk2_0),esk3_0)!=k4_xboole_0(k2_xboole_0(esk4_0,esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.52  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.52  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.52  cnf(c_0_11, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.52  cnf(c_0_12, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.52  cnf(c_0_13, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_9])).
% 0.20/0.52  cnf(c_0_14, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.52  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.52  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_12])).
% 0.20/0.52  cnf(c_0_17, negated_conjecture, (~r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.52  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.20/0.52  fof(c_0_19, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.52  fof(c_0_20, plain, ![X16, X17, X18]:k4_xboole_0(k2_xboole_0(X16,X17),X18)=k2_xboole_0(k4_xboole_0(X16,X18),k4_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.20/0.52  cnf(c_0_21, negated_conjecture, (k4_xboole_0(X1,esk2_0)=X1|~r2_hidden(esk1_3(X1,esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.52  cnf(c_0_22, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk4_0,esk2_0),esk3_0)!=k4_xboole_0(k2_xboole_0(esk4_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.52  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.52  cnf(c_0_24, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.52  cnf(c_0_25, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.20/0.52  cnf(c_0_26, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0))!=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.20/0.52  cnf(c_0_27, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0))=k4_xboole_0(k2_xboole_0(esk3_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.52  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])]), ['proof']).
% 0.20/0.52  # SZS output end CNFRefutation
% 0.20/0.52  # Proof object total steps             : 29
% 0.20/0.52  # Proof object clause steps            : 18
% 0.20/0.52  # Proof object formula steps           : 11
% 0.20/0.52  # Proof object conjectures             : 12
% 0.20/0.52  # Proof object clause conjectures      : 9
% 0.20/0.52  # Proof object formula conjectures     : 3
% 0.20/0.52  # Proof object initial clauses used    : 8
% 0.20/0.52  # Proof object initial formulas used   : 5
% 0.20/0.52  # Proof object generating inferences   : 7
% 0.20/0.52  # Proof object simplifying inferences  : 6
% 0.20/0.52  # Training examples: 0 positive, 0 negative
% 0.20/0.52  # Parsed axioms                        : 5
% 0.20/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.52  # Initial clauses                      : 12
% 0.20/0.52  # Removed in clause preprocessing      : 0
% 0.20/0.52  # Initial clauses in saturation        : 12
% 0.20/0.52  # Processed clauses                    : 794
% 0.20/0.52  # ...of these trivial                  : 88
% 0.20/0.52  # ...subsumed                          : 391
% 0.20/0.52  # ...remaining for further processing  : 315
% 0.20/0.52  # Other redundant clauses eliminated   : 3
% 0.20/0.52  # Clauses deleted for lack of memory   : 0
% 0.20/0.52  # Backward-subsumed                    : 0
% 0.20/0.52  # Backward-rewritten                   : 31
% 0.20/0.52  # Generated clauses                    : 11408
% 0.20/0.52  # ...of the previous two non-trivial   : 9898
% 0.20/0.52  # Contextual simplify-reflections      : 2
% 0.20/0.52  # Paramodulations                      : 11395
% 0.20/0.52  # Factorizations                       : 10
% 0.20/0.52  # Equation resolutions                 : 3
% 0.20/0.52  # Propositional unsat checks           : 0
% 0.20/0.52  #    Propositional check models        : 0
% 0.20/0.52  #    Propositional check unsatisfiable : 0
% 0.20/0.52  #    Propositional clauses             : 0
% 0.20/0.52  #    Propositional clauses after purity: 0
% 0.20/0.52  #    Propositional unsat core size     : 0
% 0.20/0.52  #    Propositional preprocessing time  : 0.000
% 0.20/0.52  #    Propositional encoding time       : 0.000
% 0.20/0.52  #    Propositional solver time         : 0.000
% 0.20/0.52  #    Success case prop preproc time    : 0.000
% 0.20/0.52  #    Success case prop encoding time   : 0.000
% 0.20/0.52  #    Success case prop solver time     : 0.000
% 0.20/0.52  # Current number of processed clauses  : 269
% 0.20/0.52  #    Positive orientable unit clauses  : 151
% 0.20/0.52  #    Positive unorientable unit clauses: 3
% 0.20/0.52  #    Negative unit clauses             : 6
% 0.20/0.52  #    Non-unit-clauses                  : 109
% 0.20/0.52  # Current number of unprocessed clauses: 9056
% 0.20/0.52  # ...number of literals in the above   : 15040
% 0.20/0.52  # Current number of archived formulas  : 0
% 0.20/0.52  # Current number of archived clauses   : 43
% 0.20/0.52  # Clause-clause subsumption calls (NU) : 4783
% 0.20/0.52  # Rec. Clause-clause subsumption calls : 4609
% 0.20/0.52  # Non-unit clause-clause subsumptions  : 195
% 0.20/0.52  # Unit Clause-clause subsumption calls : 234
% 0.20/0.52  # Rewrite failures with RHS unbound    : 182
% 0.20/0.52  # BW rewrite match attempts            : 3295
% 0.20/0.52  # BW rewrite match successes           : 49
% 0.20/0.52  # Condensation attempts                : 0
% 0.20/0.52  # Condensation successes               : 0
% 0.20/0.52  # Termbank termtop insertions          : 431634
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.174 s
% 0.20/0.54  # System time              : 0.010 s
% 0.20/0.54  # Total time               : 0.184 s
% 0.20/0.54  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
