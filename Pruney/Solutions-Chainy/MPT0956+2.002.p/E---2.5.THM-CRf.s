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
% DateTime   : Thu Dec  3 11:00:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  37 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 123 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(t2_wellord2,axiom,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(t29_wellord2,conjecture,(
    ! [X1] : r1_relat_2(k1_wellord2(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16] :
      ( ( k3_relat_1(X14) = X13
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X14)
        | r1_tarski(X15,X16)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(X15,X16)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk4_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X13,X14),esk4_2(X13,X14)),X14)
        | ~ r1_tarski(esk3_2(X13,X14),esk4_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk3_2(X13,X14),esk4_2(X13,X14)),X14)
        | r1_tarski(esk3_2(X13,X14),esk4_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_7,plain,(
    ! [X19] : v1_relat_1(k1_wellord2(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ( ~ v1_relat_2(X10)
        | ~ r2_hidden(X11,k3_relat_1(X10))
        | r2_hidden(k4_tarski(X11,X11),X10)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk2_1(X10),k3_relat_1(X10))
        | v1_relat_2(X10)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X10),esk2_1(X10)),X10)
        | v1_relat_2(X10)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_9,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X20] : v1_relat_2(k1_wellord2(X20)) ),
    inference(variable_rename,[status(thm)],[t2_wellord2])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r1_relat_2(X5,X6)
        | ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(X7,X7),X5)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(esk1_2(X5,X8),X8)
        | r1_relat_2(X5,X8)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X8),esk1_2(X5,X8)),X5)
        | r1_relat_2(X5,X8)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])])).

cnf(c_0_15,plain,
    ( v1_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] : r1_relat_2(k1_wellord2(X1),X1) ),
    inference(assume_negation,[status(cth)],[t29_wellord2])).

cnf(c_0_17,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X1),k1_wellord2(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_10])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,(
    ~ r1_relat_2(k1_wellord2(esk5_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_21,plain,
    ( r1_relat_2(k1_wellord2(X1),X2)
    | ~ r2_hidden(esk1_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_10])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(k1_wellord2(X1),X2),X2)
    | r1_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_relat_2(k1_wellord2(esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r1_relat_2(k1_wellord2(X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.37  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 0.20/0.37  fof(t2_wellord2, axiom, ![X1]:v1_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord2)).
% 0.20/0.37  fof(d1_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_relat_2(X1,X2)<=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(k4_tarski(X3,X3),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 0.20/0.37  fof(t29_wellord2, conjecture, ![X1]:r1_relat_2(k1_wellord2(X1),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord2)).
% 0.20/0.37  fof(c_0_6, plain, ![X13, X14, X15, X16]:(((k3_relat_1(X14)=X13|X14!=k1_wellord2(X13)|~v1_relat_1(X14))&((~r2_hidden(k4_tarski(X15,X16),X14)|r1_tarski(X15,X16)|(~r2_hidden(X15,X13)|~r2_hidden(X16,X13))|X14!=k1_wellord2(X13)|~v1_relat_1(X14))&(~r1_tarski(X15,X16)|r2_hidden(k4_tarski(X15,X16),X14)|(~r2_hidden(X15,X13)|~r2_hidden(X16,X13))|X14!=k1_wellord2(X13)|~v1_relat_1(X14))))&(((r2_hidden(esk3_2(X13,X14),X13)|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))&(r2_hidden(esk4_2(X13,X14),X13)|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14)))&((~r2_hidden(k4_tarski(esk3_2(X13,X14),esk4_2(X13,X14)),X14)|~r1_tarski(esk3_2(X13,X14),esk4_2(X13,X14))|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk3_2(X13,X14),esk4_2(X13,X14)),X14)|r1_tarski(esk3_2(X13,X14),esk4_2(X13,X14))|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.37  fof(c_0_7, plain, ![X19]:v1_relat_1(k1_wellord2(X19)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.37  fof(c_0_8, plain, ![X10, X11]:((~v1_relat_2(X10)|(~r2_hidden(X11,k3_relat_1(X10))|r2_hidden(k4_tarski(X11,X11),X10))|~v1_relat_1(X10))&((r2_hidden(esk2_1(X10),k3_relat_1(X10))|v1_relat_2(X10)|~v1_relat_1(X10))&(~r2_hidden(k4_tarski(esk2_1(X10),esk2_1(X10)),X10)|v1_relat_2(X10)|~v1_relat_1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.20/0.37  cnf(c_0_9, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_10, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  fof(c_0_11, plain, ![X20]:v1_relat_2(k1_wellord2(X20)), inference(variable_rename,[status(thm)],[t2_wellord2])).
% 0.20/0.37  fof(c_0_12, plain, ![X5, X6, X7, X8]:((~r1_relat_2(X5,X6)|(~r2_hidden(X7,X6)|r2_hidden(k4_tarski(X7,X7),X5))|~v1_relat_1(X5))&((r2_hidden(esk1_2(X5,X8),X8)|r1_relat_2(X5,X8)|~v1_relat_1(X5))&(~r2_hidden(k4_tarski(esk1_2(X5,X8),esk1_2(X5,X8)),X5)|r1_relat_2(X5,X8)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).
% 0.20/0.37  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_14, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])])).
% 0.20/0.37  cnf(c_0_15, plain, (v1_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_16, negated_conjecture, ~(![X1]:r1_relat_2(k1_wellord2(X1),X1)), inference(assume_negation,[status(cth)],[t29_wellord2])).
% 0.20/0.37  cnf(c_0_17, plain, (r1_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X1),k1_wellord2(X2))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_10])])).
% 0.20/0.37  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  fof(c_0_20, negated_conjecture, ~r1_relat_2(k1_wellord2(esk5_0),esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.37  cnf(c_0_21, plain, (r1_relat_2(k1_wellord2(X1),X2)|~r2_hidden(esk1_2(k1_wellord2(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_10])])).
% 0.20/0.37  cnf(c_0_22, plain, (r2_hidden(esk1_2(k1_wellord2(X1),X2),X2)|r1_relat_2(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_10])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (~r1_relat_2(k1_wellord2(esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_24, plain, (r1_relat_2(k1_wellord2(X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 26
% 0.20/0.37  # Proof object clause steps            : 13
% 0.20/0.37  # Proof object formula steps           : 13
% 0.20/0.37  # Proof object conjectures             : 5
% 0.20/0.37  # Proof object clause conjectures      : 2
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 7
% 0.20/0.37  # Proof object initial formulas used   : 6
% 0.20/0.37  # Proof object generating inferences   : 4
% 0.20/0.37  # Proof object simplifying inferences  : 10
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 6
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 16
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 16
% 0.20/0.37  # Processed clauses                    : 38
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 38
% 0.20/0.37  # Other redundant clauses eliminated   : 7
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 1
% 0.20/0.37  # Generated clauses                    : 17
% 0.20/0.37  # ...of the previous two non-trivial   : 14
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 10
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 7
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 14
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 10
% 0.20/0.37  # Current number of unprocessed clauses: 8
% 0.20/0.37  # ...number of literals in the above   : 31
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 17
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 46
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 24
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 2
% 0.20/0.37  # BW rewrite match successes           : 1
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1613
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.026 s
% 0.20/0.37  # System time              : 0.006 s
% 0.20/0.37  # Total time               : 0.032 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
