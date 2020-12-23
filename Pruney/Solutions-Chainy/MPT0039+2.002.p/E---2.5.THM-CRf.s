%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:00 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   28 (  83 expanded)
%              Number of clauses        :   19 (  41 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 457 expanded)
%              Number of equality atoms :   36 ( 156 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t32_xboole_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_4,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t32_xboole_1])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),k4_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X1,X2,X2),X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(X1,esk4_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk4_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = esk3_0
    | r2_hidden(esk1_3(X1,esk3_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:52:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.36/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.36/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.36/0.52  #
% 0.36/0.52  # Preprocessing time       : 0.027 s
% 0.36/0.52  # Presaturation interreduction done
% 0.36/0.52  
% 0.36/0.52  # Proof found!
% 0.36/0.52  # SZS status Theorem
% 0.36/0.52  # SZS output start CNFRefutation
% 0.36/0.52  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.36/0.52  fof(t32_xboole_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.36/0.52  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.36/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.36/0.52  fof(c_0_4, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.36/0.52  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t32_xboole_1])).
% 0.36/0.52  fof(c_0_6, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.36/0.52  cnf(c_0_7, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.36/0.52  fof(c_0_8, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.36/0.52  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.36/0.52  cnf(c_0_10, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.36/0.52  cnf(c_0_11, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.36/0.52  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_7])).
% 0.36/0.52  cnf(c_0_13, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.52  cnf(c_0_14, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_9])).
% 0.36/0.52  cnf(c_0_15, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_10])).
% 0.36/0.52  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_11])).
% 0.36/0.52  cnf(c_0_17, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.36/0.52  cnf(c_0_18, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.36/0.52  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),k4_xboole_0(X2,X3))|r2_hidden(esk1_3(X1,X2,X2),X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.36/0.52  fof(c_0_20, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.36/0.52  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_16]), c_0_16])).
% 0.36/0.52  cnf(c_0_22, negated_conjecture, (k3_xboole_0(X1,esk4_0)=esk4_0|r2_hidden(esk1_3(X1,esk4_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.36/0.52  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.36/0.52  cnf(c_0_24, negated_conjecture, (k3_xboole_0(X1,esk3_0)=esk3_0|r2_hidden(esk1_3(X1,esk3_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_18])).
% 0.36/0.52  cnf(c_0_25, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.36/0.52  cnf(c_0_26, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.52  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_24]), c_0_25]), c_0_26]), ['proof']).
% 0.36/0.52  # SZS output end CNFRefutation
% 0.36/0.52  # Proof object total steps             : 28
% 0.36/0.52  # Proof object clause steps            : 19
% 0.36/0.52  # Proof object formula steps           : 9
% 0.36/0.52  # Proof object conjectures             : 10
% 0.36/0.52  # Proof object clause conjectures      : 7
% 0.36/0.52  # Proof object formula conjectures     : 3
% 0.36/0.52  # Proof object initial clauses used    : 8
% 0.36/0.52  # Proof object initial formulas used   : 4
% 0.36/0.52  # Proof object generating inferences   : 8
% 0.36/0.52  # Proof object simplifying inferences  : 9
% 0.36/0.52  # Training examples: 0 positive, 0 negative
% 0.36/0.52  # Parsed axioms                        : 4
% 0.36/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.36/0.52  # Initial clauses                      : 15
% 0.36/0.52  # Removed in clause preprocessing      : 0
% 0.36/0.52  # Initial clauses in saturation        : 15
% 0.36/0.52  # Processed clauses                    : 1552
% 0.36/0.52  # ...of these trivial                  : 63
% 0.36/0.52  # ...subsumed                          : 1219
% 0.36/0.52  # ...remaining for further processing  : 270
% 0.36/0.52  # Other redundant clauses eliminated   : 6
% 0.36/0.52  # Clauses deleted for lack of memory   : 0
% 0.36/0.52  # Backward-subsumed                    : 7
% 0.36/0.52  # Backward-rewritten                   : 8
% 0.36/0.52  # Generated clauses                    : 11894
% 0.36/0.52  # ...of the previous two non-trivial   : 9660
% 0.36/0.52  # Contextual simplify-reflections      : 5
% 0.36/0.52  # Paramodulations                      : 11818
% 0.36/0.52  # Factorizations                       : 70
% 0.36/0.52  # Equation resolutions                 : 6
% 0.36/0.52  # Propositional unsat checks           : 0
% 0.36/0.52  #    Propositional check models        : 0
% 0.36/0.52  #    Propositional check unsatisfiable : 0
% 0.36/0.52  #    Propositional clauses             : 0
% 0.36/0.52  #    Propositional clauses after purity: 0
% 0.36/0.52  #    Propositional unsat core size     : 0
% 0.36/0.52  #    Propositional preprocessing time  : 0.000
% 0.36/0.52  #    Propositional encoding time       : 0.000
% 0.36/0.52  #    Propositional solver time         : 0.000
% 0.36/0.52  #    Success case prop preproc time    : 0.000
% 0.36/0.52  #    Success case prop encoding time   : 0.000
% 0.36/0.52  #    Success case prop solver time     : 0.000
% 0.36/0.52  # Current number of processed clauses  : 234
% 0.36/0.52  #    Positive orientable unit clauses  : 56
% 0.36/0.52  #    Positive unorientable unit clauses: 3
% 0.36/0.52  #    Negative unit clauses             : 3
% 0.36/0.52  #    Non-unit-clauses                  : 172
% 0.36/0.52  # Current number of unprocessed clauses: 8120
% 0.36/0.52  # ...number of literals in the above   : 24366
% 0.36/0.52  # Current number of archived formulas  : 0
% 0.36/0.52  # Current number of archived clauses   : 30
% 0.36/0.52  # Clause-clause subsumption calls (NU) : 5523
% 0.36/0.52  # Rec. Clause-clause subsumption calls : 3558
% 0.36/0.52  # Non-unit clause-clause subsumptions  : 460
% 0.36/0.52  # Unit Clause-clause subsumption calls : 228
% 0.36/0.52  # Rewrite failures with RHS unbound    : 31
% 0.36/0.52  # BW rewrite match attempts            : 137
% 0.36/0.52  # BW rewrite match successes           : 13
% 0.36/0.52  # Condensation attempts                : 0
% 0.36/0.52  # Condensation successes               : 0
% 0.36/0.52  # Termbank termtop insertions          : 168518
% 0.36/0.53  
% 0.36/0.53  # -------------------------------------------------
% 0.36/0.53  # User time                : 0.169 s
% 0.36/0.53  # System time              : 0.006 s
% 0.36/0.53  # Total time               : 0.175 s
% 0.36/0.53  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
