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
% DateTime   : Thu Dec  3 11:00:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  54 expanded)
%              Number of clauses        :   15 (  23 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 184 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t91_mcart_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
            & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_7,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(X16,k2_zfmisc_1(k1_relat_1(X16),k2_relat_1(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
              & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_mcart_1])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] :
      ( ( r2_hidden(k1_mcart_1(X17),X18)
        | ~ r2_hidden(X17,k2_zfmisc_1(X18,X19)) )
      & ( r2_hidden(k2_mcart_1(X17),X19)
        | ~ r2_hidden(X17,k2_zfmisc_1(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r2_hidden(esk3_0,esk2_0)
    & ( ~ r2_hidden(k1_mcart_1(esk3_0),k1_relat_1(esk2_0))
      | ~ r2_hidden(k2_mcart_1(esk3_0),k2_relat_1(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk3_0),k1_relat_1(esk2_0))
    | ~ r2_hidden(k2_mcart_1(esk3_0),k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_24,plain,
    ( r2_hidden(k1_mcart_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.039 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.39  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.19/0.39  fof(t91_mcart_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(r2_hidden(X2,X1)=>(r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))&r2_hidden(k2_mcart_1(X2),k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_mcart_1)).
% 0.19/0.39  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.39  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_6, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.39  fof(c_0_7, plain, ![X16]:(~v1_relat_1(X16)|r1_tarski(X16,k2_zfmisc_1(k1_relat_1(X16),k2_relat_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.19/0.39  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_9, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_10, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(r2_hidden(X2,X1)=>(r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))&r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)))))), inference(assume_negation,[status(cth)],[t91_mcart_1])).
% 0.19/0.39  fof(c_0_12, plain, ![X17, X18, X19]:((r2_hidden(k1_mcart_1(X17),X18)|~r2_hidden(X17,k2_zfmisc_1(X18,X19)))&(r2_hidden(k2_mcart_1(X17),X19)|~r2_hidden(X17,k2_zfmisc_1(X18,X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.39  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_14, plain, (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.39  fof(c_0_15, negated_conjecture, (v1_relat_1(esk2_0)&(r2_hidden(esk3_0,esk2_0)&(~r2_hidden(k1_mcart_1(esk3_0),k1_relat_1(esk2_0))|~r2_hidden(k2_mcart_1(esk3_0),k2_relat_1(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.39  cnf(c_0_16, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_17, plain, (r2_hidden(X1,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (~r2_hidden(k1_mcart_1(esk3_0),k1_relat_1(esk2_0))|~r2_hidden(k2_mcart_1(esk3_0),k2_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_19, plain, (r2_hidden(k2_mcart_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_22, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (~r2_hidden(k1_mcart_1(esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.19/0.39  cnf(c_0_24, plain, (r2_hidden(k1_mcart_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20]), c_0_21])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 26
% 0.19/0.39  # Proof object clause steps            : 15
% 0.19/0.39  # Proof object formula steps           : 11
% 0.19/0.39  # Proof object conjectures             : 8
% 0.19/0.39  # Proof object clause conjectures      : 5
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 8
% 0.19/0.39  # Proof object initial formulas used   : 5
% 0.19/0.39  # Proof object generating inferences   : 6
% 0.19/0.39  # Proof object simplifying inferences  : 7
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 5
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 13
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 13
% 0.19/0.39  # Processed clauses                    : 26
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 3
% 0.19/0.39  # ...remaining for further processing  : 23
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 48
% 0.19/0.39  # ...of the previous two non-trivial   : 41
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 42
% 0.19/0.39  # Factorizations                       : 4
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 21
% 0.19/0.39  #    Positive orientable unit clauses  : 3
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 17
% 0.19/0.39  # Current number of unprocessed clauses: 28
% 0.19/0.39  # ...number of literals in the above   : 79
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 0
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 46
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 38
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.39  # Unit Clause-clause subsumption calls : 7
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 3
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 1385
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.041 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.046 s
% 0.19/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
