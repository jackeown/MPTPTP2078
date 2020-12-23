%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  52 expanded)
%              Number of clauses        :   15 (  21 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  91 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

fof(c_0_9,plain,(
    ! [X82,X83] :
      ( ~ v1_relat_1(X83)
      | ~ r1_tarski(k2_relat_1(X83),X82)
      | k5_relat_1(X83,k6_relat_1(X82)) = X83 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_10,plain,(
    ! [X81] :
      ( k1_relat_1(k6_relat_1(X81)) = X81
      & k2_relat_1(k6_relat_1(X81)) = X81 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_11,plain,(
    ! [X86] :
      ( v1_relat_1(k6_relat_1(X86))
      & v4_relat_1(k6_relat_1(X86),X86)
      & v5_relat_1(k6_relat_1(X86),X86) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

fof(c_0_12,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk4_0),k6_relat_1(esk3_0)) != k6_relat_1(k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_14,plain,(
    ! [X84,X85] :
      ( ~ v1_relat_1(X85)
      | k7_relat_1(X85,X84) = k5_relat_1(k6_relat_1(X84),X85) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_15,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk4_0),k6_relat_1(esk3_0)) != k6_relat_1(k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X79,X80] :
      ( ~ v1_relat_1(X80)
      | k7_relat_1(X80,X79) = k7_relat_1(X80,k3_xboole_0(k1_relat_1(X80),X79)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_23,plain,(
    ! [X35,X36] : r1_tarski(k3_xboole_0(X35,X36),X35) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_24,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk4_0),k6_relat_1(esk3_0)) != k6_relat_1(k3_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

cnf(c_0_27,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk3_0),esk4_0) != k6_relat_1(k3_xboole_0(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_17])])).

cnf(c_0_30,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_17]),c_0_27]),c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S069N
% 0.20/0.39  # and selection function SelectComplexAHPExceptRRHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.20/0.39  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.20/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.39  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.20/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.39  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.39  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 0.20/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.20/0.39  fof(c_0_9, plain, ![X82, X83]:(~v1_relat_1(X83)|(~r1_tarski(k2_relat_1(X83),X82)|k5_relat_1(X83,k6_relat_1(X82))=X83)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.20/0.39  fof(c_0_10, plain, ![X81]:(k1_relat_1(k6_relat_1(X81))=X81&k2_relat_1(k6_relat_1(X81))=X81), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.39  fof(c_0_11, plain, ![X86]:((v1_relat_1(k6_relat_1(X86))&v4_relat_1(k6_relat_1(X86),X86))&v5_relat_1(k6_relat_1(X86),X86)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.20/0.39  fof(c_0_12, negated_conjecture, k5_relat_1(k6_relat_1(esk4_0),k6_relat_1(esk3_0))!=k6_relat_1(k3_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.39  fof(c_0_13, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.39  fof(c_0_14, plain, ![X84, X85]:(~v1_relat_1(X85)|k7_relat_1(X85,X84)=k5_relat_1(k6_relat_1(X84),X85)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.39  cnf(c_0_15, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_16, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_17, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (k5_relat_1(k6_relat_1(esk4_0),k6_relat_1(esk3_0))!=k6_relat_1(k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  fof(c_0_20, plain, ![X79, X80]:(~v1_relat_1(X80)|k7_relat_1(X80,X79)=k7_relat_1(X80,k3_xboole_0(k1_relat_1(X80),X79))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.20/0.39  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_22, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.20/0.39  fof(c_0_23, plain, ![X35, X36]:r1_tarski(k3_xboole_0(X35,X36),X35), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k5_relat_1(k6_relat_1(esk4_0),k6_relat_1(esk3_0))!=k6_relat_1(k3_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_25, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_26, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.20/0.39  cnf(c_0_27, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (k7_relat_1(k6_relat_1(esk3_0),esk4_0)!=k6_relat_1(k3_xboole_0(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_17])])).
% 0.20/0.39  cnf(c_0_30, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_17]), c_0_27]), c_0_28])])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_19])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 32
% 0.20/0.39  # Proof object clause steps            : 15
% 0.20/0.39  # Proof object formula steps           : 17
% 0.20/0.39  # Proof object conjectures             : 7
% 0.20/0.39  # Proof object clause conjectures      : 4
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 9
% 0.20/0.39  # Proof object initial formulas used   : 8
% 0.20/0.39  # Proof object generating inferences   : 4
% 0.20/0.39  # Proof object simplifying inferences  : 15
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 35
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 47
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 45
% 0.20/0.39  # Processed clauses                    : 139
% 0.20/0.39  # ...of these trivial                  : 10
% 0.20/0.39  # ...subsumed                          : 12
% 0.20/0.39  # ...remaining for further processing  : 117
% 0.20/0.39  # Other redundant clauses eliminated   : 10
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 6
% 0.20/0.39  # Generated clauses                    : 1153
% 0.20/0.39  # ...of the previous two non-trivial   : 1017
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 1144
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 10
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
% 0.20/0.39  # Current number of processed clauses  : 61
% 0.20/0.39  #    Positive orientable unit clauses  : 32
% 0.20/0.39  #    Positive unorientable unit clauses: 3
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 25
% 0.20/0.39  # Current number of unprocessed clauses: 966
% 0.20/0.39  # ...number of literals in the above   : 2195
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 53
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 260
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 160
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.20/0.39  # Unit Clause-clause subsumption calls : 11
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 55
% 0.20/0.39  # BW rewrite match successes           : 30
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 19638
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.053 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.057 s
% 0.20/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
