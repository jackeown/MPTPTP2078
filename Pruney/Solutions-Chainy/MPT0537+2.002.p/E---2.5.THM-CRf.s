%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:15 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   23 (  42 expanded)
%              Number of clauses        :   12 (  20 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 131 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t137_relat_1])).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X14,X10)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X13,X14),X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,X10)
        | ~ r2_hidden(k4_tarski(X15,X16),X11)
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | ~ r2_hidden(esk2_3(X10,X11,X12),X10)
        | ~ r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_3(X10,X11,X12),X10)
        | r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)
        | r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & k8_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X19,X20,X23,X25,X26] :
      ( ( ~ v1_relat_1(X19)
        | ~ r2_hidden(X20,X19)
        | X20 = k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)) )
      & ( r2_hidden(esk5_1(X23),X23)
        | v1_relat_1(X23) )
      & ( esk5_1(X23) != k4_tarski(X25,X26)
        | v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk6_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk6_0,X1),esk2_3(X2,esk6_0,X1)),X1)
    | r2_hidden(esk2_3(X2,esk6_0,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk6_0)
    | r2_hidden(k4_tarski(esk1_3(X2,esk6_0,X1),esk2_3(X2,esk6_0,X1)),X1)
    | r2_hidden(esk2_3(X2,esk6_0,X1),X2)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k8_relat_1(X1,esk6_0) = k1_xboole_0
    | r2_hidden(esk2_3(X1,esk6_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( k8_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n024.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 19:32:51 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.31  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.17/0.35  # and selection function SelectCQIArNXTEqFirst.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.027 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t137_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 0.17/0.35  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.17/0.35  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 0.17/0.35  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.17/0.35  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.17/0.35  fof(c_0_5, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t137_relat_1])).
% 0.17/0.35  fof(c_0_6, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.17/0.35  fof(c_0_7, plain, ![X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X14,X10)|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X13,X14),X11)|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11)))&(~r2_hidden(X16,X10)|~r2_hidden(k4_tarski(X15,X16),X11)|r2_hidden(k4_tarski(X15,X16),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11)))&((~r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|(~r2_hidden(esk2_3(X10,X11,X12),X10)|~r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11))|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&((r2_hidden(esk2_3(X10,X11,X12),X10)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.17/0.35  fof(c_0_8, negated_conjecture, (v1_relat_1(esk6_0)&k8_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.17/0.35  fof(c_0_9, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.17/0.35  cnf(c_0_10, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.35  cnf(c_0_11, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.35  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.35  fof(c_0_13, plain, ![X19, X20, X23, X25, X26]:((~v1_relat_1(X19)|(~r2_hidden(X20,X19)|X20=k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20))))&((r2_hidden(esk5_1(X23),X23)|v1_relat_1(X23))&(esk5_1(X23)!=k4_tarski(X25,X26)|v1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.17/0.35  cnf(c_0_14, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.35  cnf(c_0_15, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_16, negated_conjecture, (X1=k8_relat_1(X2,esk6_0)|r2_hidden(k4_tarski(esk1_3(X2,esk6_0,X1),esk2_3(X2,esk6_0,X1)),X1)|r2_hidden(esk2_3(X2,esk6_0,X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.17/0.35  cnf(c_0_17, plain, (r2_hidden(esk5_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.35  cnf(c_0_18, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.35  cnf(c_0_19, negated_conjecture, (X1=k8_relat_1(X2,esk6_0)|r2_hidden(k4_tarski(esk1_3(X2,esk6_0,X1),esk2_3(X2,esk6_0,X1)),X1)|r2_hidden(esk2_3(X2,esk6_0,X1),X2)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.17/0.35  cnf(c_0_20, negated_conjecture, (k8_relat_1(X1,esk6_0)=k1_xboole_0|r2_hidden(esk2_3(X1,esk6_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_18])).
% 0.17/0.35  cnf(c_0_21, negated_conjecture, (k8_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.35  cnf(c_0_22, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_20]), c_0_21]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 23
% 0.17/0.35  # Proof object clause steps            : 12
% 0.17/0.35  # Proof object formula steps           : 11
% 0.17/0.35  # Proof object conjectures             : 9
% 0.17/0.35  # Proof object clause conjectures      : 6
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 6
% 0.17/0.35  # Proof object initial formulas used   : 5
% 0.17/0.35  # Proof object generating inferences   : 5
% 0.17/0.35  # Proof object simplifying inferences  : 3
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 5
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 15
% 0.17/0.35  # Removed in clause preprocessing      : 0
% 0.17/0.35  # Initial clauses in saturation        : 15
% 0.17/0.35  # Processed clauses                    : 62
% 0.17/0.35  # ...of these trivial                  : 0
% 0.17/0.35  # ...subsumed                          : 6
% 0.17/0.35  # ...remaining for further processing  : 56
% 0.17/0.35  # Other redundant clauses eliminated   : 5
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 1
% 0.17/0.35  # Backward-rewritten                   : 0
% 0.17/0.35  # Generated clauses                    : 57
% 0.17/0.35  # ...of the previous two non-trivial   : 55
% 0.17/0.35  # Contextual simplify-reflections      : 0
% 0.17/0.35  # Paramodulations                      : 52
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 5
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 35
% 0.17/0.35  #    Positive orientable unit clauses  : 3
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 4
% 0.17/0.35  #    Non-unit-clauses                  : 28
% 0.17/0.35  # Current number of unprocessed clauses: 20
% 0.17/0.35  # ...number of literals in the above   : 89
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 16
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 377
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 91
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 6
% 0.17/0.35  # Unit Clause-clause subsumption calls : 1
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 0
% 0.17/0.35  # BW rewrite match successes           : 0
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 2914
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.028 s
% 0.17/0.35  # System time              : 0.006 s
% 0.17/0.35  # Total time               : 0.034 s
% 0.17/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
