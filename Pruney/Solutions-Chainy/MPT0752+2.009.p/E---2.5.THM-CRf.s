%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:36 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 (  76 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_ordinal1,conjecture,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(l222_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(cc4_ordinal1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v5_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X1)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    inference(assume_negation,[status(cth)],[t45_ordinal1])).

fof(c_0_11,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk4_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X19,X20] :
      ( v4_relat_1(k1_xboole_0,X19)
      & v5_relat_1(k1_xboole_0,X20) ) ),
    inference(variable_rename,[status(thm)],[l222_relat_1])).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,k1_tarski(X10)) != X9
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(X10,X9)
        | k4_xboole_0(X9,k1_tarski(X10)) = X9 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_14,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk4_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X22] :
      ( ~ v1_xboole_0(X22)
      | v5_ordinal1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_ordinal1])])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_23,negated_conjecture,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_24,plain,
    ( v5_ordinal1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_26,plain,(
    ! [X21] :
      ( ~ v1_xboole_0(X21)
      | v1_funct_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_enumset1(X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X11,X12,X15,X17,X18] :
      ( ( ~ v1_relat_1(X11)
        | ~ r2_hidden(X12,X11)
        | X12 = k4_tarski(esk1_2(X11,X12),esk2_2(X11,X12)) )
      & ( r2_hidden(esk3_1(X15),X15)
        | v1_relat_1(X15) )
      & ( esk3_1(X15) != k4_tarski(X17,X18)
        | v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25])])).

cnf(c_0_35,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n013.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 14:26:24 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  # Version: 2.5pre002
% 0.11/0.31  # No SInE strategy applied
% 0.11/0.31  # Trying AutoSched0 for 299 seconds
% 0.15/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.15/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.15/0.34  #
% 0.15/0.34  # Preprocessing time       : 0.026 s
% 0.15/0.34  # Presaturation interreduction done
% 0.15/0.34  
% 0.15/0.34  # Proof found!
% 0.15/0.34  # SZS status Theorem
% 0.15/0.34  # SZS output start CNFRefutation
% 0.15/0.34  fof(t45_ordinal1, conjecture, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.15/0.34  fof(l222_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 0.15/0.34  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.15/0.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.34  fof(cc4_ordinal1, axiom, ![X1]:(v1_xboole_0(X1)=>v5_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_ordinal1)).
% 0.15/0.34  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.15/0.34  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.15/0.34  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.15/0.34  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.15/0.34  fof(c_0_10, negated_conjecture, ~(![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0))), inference(assume_negation,[status(cth)],[t45_ordinal1])).
% 0.15/0.34  fof(c_0_11, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk4_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.15/0.34  fof(c_0_12, plain, ![X19, X20]:(v4_relat_1(k1_xboole_0,X19)&v5_relat_1(k1_xboole_0,X20)), inference(variable_rename,[status(thm)],[l222_relat_1])).
% 0.15/0.34  fof(c_0_13, plain, ![X9, X10]:((k4_xboole_0(X9,k1_tarski(X10))!=X9|~r2_hidden(X10,X9))&(r2_hidden(X10,X9)|k4_xboole_0(X9,k1_tarski(X10))=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.15/0.34  fof(c_0_14, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.34  fof(c_0_15, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.34  cnf(c_0_16, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk4_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_17, plain, (v5_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.34  fof(c_0_18, plain, ![X22]:(~v1_xboole_0(X22)|v5_ordinal1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_ordinal1])])).
% 0.15/0.34  cnf(c_0_19, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.34  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.34  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.34  fof(c_0_22, plain, ![X5]:k4_xboole_0(k1_xboole_0,X5)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.15/0.34  cnf(c_0_23, negated_conjecture, (~v5_ordinal1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17])])).
% 0.15/0.34  cnf(c_0_24, plain, (v5_ordinal1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.34  cnf(c_0_25, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.15/0.34  fof(c_0_26, plain, ![X21]:(~v1_xboole_0(X21)|v1_funct_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.15/0.34  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_enumset1(X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.15/0.34  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.34  fof(c_0_29, plain, ![X11, X12, X15, X17, X18]:((~v1_relat_1(X11)|(~r2_hidden(X12,X11)|X12=k4_tarski(esk1_2(X11,X12),esk2_2(X11,X12))))&((r2_hidden(esk3_1(X15),X15)|v1_relat_1(X15))&(esk3_1(X15)!=k4_tarski(X17,X18)|v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.15/0.34  cnf(c_0_30, negated_conjecture, (~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.15/0.34  cnf(c_0_31, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.15/0.34  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.15/0.34  cnf(c_0_33, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_34, negated_conjecture, (~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_25])])).
% 0.15/0.34  cnf(c_0_35, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.15/0.34  # SZS output end CNFRefutation
% 0.15/0.34  # Proof object total steps             : 36
% 0.15/0.34  # Proof object clause steps            : 16
% 0.15/0.34  # Proof object formula steps           : 20
% 0.15/0.34  # Proof object conjectures             : 7
% 0.15/0.34  # Proof object clause conjectures      : 4
% 0.15/0.34  # Proof object formula conjectures     : 3
% 0.15/0.34  # Proof object initial clauses used    : 10
% 0.15/0.34  # Proof object initial formulas used   : 10
% 0.15/0.34  # Proof object generating inferences   : 4
% 0.15/0.34  # Proof object simplifying inferences  : 9
% 0.15/0.34  # Training examples: 0 positive, 0 negative
% 0.15/0.34  # Parsed axioms                        : 10
% 0.15/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.34  # Initial clauses                      : 14
% 0.15/0.34  # Removed in clause preprocessing      : 2
% 0.15/0.34  # Initial clauses in saturation        : 12
% 0.15/0.34  # Processed clauses                    : 26
% 0.15/0.34  # ...of these trivial                  : 0
% 0.15/0.34  # ...subsumed                          : 0
% 0.15/0.34  # ...remaining for further processing  : 26
% 0.15/0.34  # Other redundant clauses eliminated   : 0
% 0.15/0.34  # Clauses deleted for lack of memory   : 0
% 0.15/0.34  # Backward-subsumed                    : 1
% 0.15/0.34  # Backward-rewritten                   : 1
% 0.15/0.34  # Generated clauses                    : 4
% 0.15/0.34  # ...of the previous two non-trivial   : 4
% 0.15/0.34  # Contextual simplify-reflections      : 0
% 0.15/0.34  # Paramodulations                      : 4
% 0.15/0.34  # Factorizations                       : 0
% 0.15/0.34  # Equation resolutions                 : 0
% 0.15/0.34  # Propositional unsat checks           : 0
% 0.15/0.34  #    Propositional check models        : 0
% 0.15/0.34  #    Propositional check unsatisfiable : 0
% 0.15/0.34  #    Propositional clauses             : 0
% 0.15/0.34  #    Propositional clauses after purity: 0
% 0.15/0.34  #    Propositional unsat core size     : 0
% 0.15/0.34  #    Propositional preprocessing time  : 0.000
% 0.15/0.34  #    Propositional encoding time       : 0.000
% 0.15/0.34  #    Propositional solver time         : 0.000
% 0.15/0.34  #    Success case prop preproc time    : 0.000
% 0.15/0.34  #    Success case prop encoding time   : 0.000
% 0.15/0.34  #    Success case prop solver time     : 0.000
% 0.15/0.34  # Current number of processed clauses  : 12
% 0.15/0.34  #    Positive orientable unit clauses  : 4
% 0.15/0.34  #    Positive unorientable unit clauses: 0
% 0.15/0.34  #    Negative unit clauses             : 2
% 0.15/0.34  #    Non-unit-clauses                  : 6
% 0.15/0.34  # Current number of unprocessed clauses: 2
% 0.15/0.34  # ...number of literals in the above   : 5
% 0.15/0.34  # Current number of archived formulas  : 0
% 0.15/0.34  # Current number of archived clauses   : 16
% 0.15/0.34  # Clause-clause subsumption calls (NU) : 5
% 0.15/0.34  # Rec. Clause-clause subsumption calls : 4
% 0.15/0.34  # Non-unit clause-clause subsumptions  : 1
% 0.15/0.34  # Unit Clause-clause subsumption calls : 1
% 0.15/0.34  # Rewrite failures with RHS unbound    : 0
% 0.15/0.34  # BW rewrite match attempts            : 1
% 0.15/0.34  # BW rewrite match successes           : 1
% 0.15/0.34  # Condensation attempts                : 0
% 0.15/0.34  # Condensation successes               : 0
% 0.15/0.34  # Termbank termtop insertions          : 774
% 0.15/0.34  
% 0.15/0.34  # -------------------------------------------------
% 0.15/0.34  # User time                : 0.029 s
% 0.15/0.34  # System time              : 0.001 s
% 0.15/0.34  # Total time               : 0.030 s
% 0.15/0.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
