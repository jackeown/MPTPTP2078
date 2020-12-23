%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  39 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 117 expanded)
%              Number of equality atoms :   39 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_mcart_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ! [X3] :
                ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
               => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t24_mcart_1])).

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X17,X19,X20] :
      ( ( r2_hidden(esk2_1(X17),X17)
        | X17 = k1_xboole_0 )
      & ( ~ r2_hidden(X19,X17)
        | esk2_1(X17) != k4_tarski(X19,X20)
        | X17 = k1_xboole_0 )
      & ( ~ r2_hidden(X20,X17)
        | esk2_1(X17) != k4_tarski(X19,X20)
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X11,X12)
      | v1_xboole_0(X12)
      | r2_hidden(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_11,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))
    & esk5_0 != k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ r2_hidden(X15,X16)
      | X15 = k4_tarski(k1_mcart_1(X15),k2_mcart_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_21,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 != k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t24_mcart_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 0.20/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.20/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.38  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.20/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))))))), inference(assume_negation,[status(cth)],[t24_mcart_1])).
% 0.20/0.38  fof(c_0_8, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X17, X19, X20]:((r2_hidden(esk2_1(X17),X17)|X17=k1_xboole_0)&((~r2_hidden(X19,X17)|esk2_1(X17)!=k4_tarski(X19,X20)|X17=k1_xboole_0)&(~r2_hidden(X20,X17)|esk2_1(X17)!=k4_tarski(X19,X20)|X17=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X11, X12]:(~m1_subset_1(X11,X12)|(v1_xboole_0(X12)|r2_hidden(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))&esk5_0!=k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.38  cnf(c_0_12, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_13, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_14, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_16, plain, ![X15, X16]:(~v1_relat_1(X16)|(~r2_hidden(X15,X16)|X15=k4_tarski(k1_mcart_1(X15),k2_mcart_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.20/0.38  cnf(c_0_17, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  fof(c_0_19, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.38  fof(c_0_20, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_21, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_23, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (esk5_0!=k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_25, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 30
% 0.20/0.38  # Proof object clause steps            : 15
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 11
% 0.20/0.38  # Proof object clause conjectures      : 8
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 10
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 5
% 0.20/0.38  # Proof object simplifying inferences  : 5
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 15
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 15
% 0.20/0.38  # Processed clauses                    : 24
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 1
% 0.20/0.38  # ...remaining for further processing  : 22
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 3
% 0.20/0.38  # Generated clauses                    : 20
% 0.20/0.38  # ...of the previous two non-trivial   : 19
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 18
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 17
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 9
% 0.20/0.38  # Current number of unprocessed clauses: 8
% 0.20/0.38  # ...number of literals in the above   : 20
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 3
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 14
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 13
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 1
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 958
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.031 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
