%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:34 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 103 expanded)
%              Number of equality atoms :   36 (  37 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t150_relat_1,conjecture,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(k4_tarski(esk1_4(X10,X11,X12,X13),X13),X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk1_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X16,X15),X10)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(esk2_3(X10,X17,X18),X18)
        | ~ r2_hidden(k4_tarski(X20,esk2_3(X10,X17,X18)),X10)
        | ~ r2_hidden(X20,X17)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk3_3(X10,X17,X18),esk2_3(X10,X17,X18)),X10)
        | r2_hidden(esk2_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_3(X10,X17,X18),X17)
        | r2_hidden(esk2_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X22,X23,X26,X28,X29] :
      ( ( ~ v1_relat_1(X22)
        | ~ r2_hidden(X23,X22)
        | X23 = k4_tarski(esk4_2(X22,X23),esk5_2(X22,X23)) )
      & ( r2_hidden(esk6_1(X26),X26)
        | v1_relat_1(X26) )
      & ( esk6_1(X26) != k4_tarski(X28,X29)
        | v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_9,plain,
    ( ~ epred2_0
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,
    ( ~ epred1_0
  <=> ! [X2] : X2 != k1_xboole_0 ),
    introduced(definition)).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( epred2_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(split_equiv,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( X1 = k9_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk3_3(X2,X3,X1),esk2_3(X2,X3,X1)),X2)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | r2_hidden(esk6_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_12]),c_0_9])).

cnf(c_0_18,plain,
    ( epred1_0
    | X1 != k1_xboole_0 ),
    inference(split_equiv,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k9_relat_1(k1_xboole_0,X2)
    | epred2_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_15])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t150_relat_1])).

cnf(c_0_21,plain,
    ( X1 != k1_xboole_0
    | ~ epred2_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | epred2_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

fof(c_0_23,negated_conjecture,(
    k9_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_24,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.14/0.38  # and selection function SelectVGNonCR.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.14/0.38  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.14/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.14/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.14/0.38  fof(t150_relat_1, conjecture, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 0.14/0.38  fof(c_0_5, plain, ![X10, X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(k4_tarski(esk1_4(X10,X11,X12,X13),X13),X10)|~r2_hidden(X13,X12)|X12!=k9_relat_1(X10,X11)|~v1_relat_1(X10))&(r2_hidden(esk1_4(X10,X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k9_relat_1(X10,X11)|~v1_relat_1(X10)))&(~r2_hidden(k4_tarski(X16,X15),X10)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k9_relat_1(X10,X11)|~v1_relat_1(X10)))&((~r2_hidden(esk2_3(X10,X17,X18),X18)|(~r2_hidden(k4_tarski(X20,esk2_3(X10,X17,X18)),X10)|~r2_hidden(X20,X17))|X18=k9_relat_1(X10,X17)|~v1_relat_1(X10))&((r2_hidden(k4_tarski(esk3_3(X10,X17,X18),esk2_3(X10,X17,X18)),X10)|r2_hidden(esk2_3(X10,X17,X18),X18)|X18=k9_relat_1(X10,X17)|~v1_relat_1(X10))&(r2_hidden(esk3_3(X10,X17,X18),X17)|r2_hidden(esk2_3(X10,X17,X18),X18)|X18=k9_relat_1(X10,X17)|~v1_relat_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.14/0.38  fof(c_0_6, plain, ![X22, X23, X26, X28, X29]:((~v1_relat_1(X22)|(~r2_hidden(X23,X22)|X23=k4_tarski(esk4_2(X22,X23),esk5_2(X22,X23))))&((r2_hidden(esk6_1(X26),X26)|v1_relat_1(X26))&(esk6_1(X26)!=k4_tarski(X28,X29)|v1_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.14/0.38  fof(c_0_8, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.14/0.38  fof(c_0_9, plain, (~epred2_0<=>![X1]:~r2_hidden(X1,k1_xboole_0)), introduced(definition)).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(esk6_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  fof(c_0_12, plain, (~epred1_0<=>![X2]:X2!=k1_xboole_0), introduced(definition)).
% 0.14/0.38  cnf(c_0_13, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_14, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_15, plain, (epred2_0|~r2_hidden(X1,k1_xboole_0)), inference(split_equiv,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_16, plain, (X1=k9_relat_1(X2,X3)|r2_hidden(k4_tarski(esk3_3(X2,X3,X1),esk2_3(X2,X3,X1)),X2)|r2_hidden(esk2_3(X2,X3,X1),X1)|r2_hidden(esk6_1(X2),X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_17, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_12]), c_0_9])).
% 0.14/0.38  cnf(c_0_18, plain, (epred1_0|X1!=k1_xboole_0), inference(split_equiv,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, plain, (X1=k9_relat_1(k1_xboole_0,X2)|epred2_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_15])).
% 0.14/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t150_relat_1])).
% 0.14/0.38  cnf(c_0_21, plain, (X1!=k1_xboole_0|~epred2_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  cnf(c_0_22, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0|epred2_0), inference(spm,[status(thm)],[c_0_15, c_0_19])).
% 0.14/0.38  fof(c_0_23, negated_conjecture, k9_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.14/0.38  cnf(c_0_24, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (k9_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_26, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 28
% 0.14/0.38  # Proof object clause steps            : 15
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 5
% 0.14/0.38  # Proof object clause conjectures      : 2
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 7
% 0.14/0.38  # Proof object initial formulas used   : 5
% 0.14/0.38  # Proof object generating inferences   : 7
% 0.14/0.38  # Proof object simplifying inferences  : 5
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 5
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 14
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 14
% 0.14/0.38  # Processed clauses                    : 114
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 19
% 0.14/0.38  # ...remaining for further processing  : 95
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 6
% 0.14/0.38  # Backward-rewritten                   : 11
% 0.14/0.38  # Generated clauses                    : 228
% 0.14/0.38  # ...of the previous two non-trivial   : 225
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 209
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 13
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 62
% 0.14/0.38  #    Positive orientable unit clauses  : 1
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 59
% 0.14/0.38  # Current number of unprocessed clauses: 134
% 0.14/0.38  # ...number of literals in the above   : 665
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 31
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1285
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 603
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 28
% 0.14/0.38  # Unit Clause-clause subsumption calls : 25
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 5
% 0.14/0.38  # BW rewrite match successes           : 5
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 5595
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.028 s
% 0.14/0.38  # System time              : 0.012 s
% 0.14/0.38  # Total time               : 0.040 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
