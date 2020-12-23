%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:00 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   29 (  63 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 235 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t177_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v2_funct_1(X1)
            & r1_tarski(X2,k1_relat_1(X1)) )
         => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v2_funct_1(X1)
              & r1_tarski(X2,k1_relat_1(X1)) )
           => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t177_funct_1])).

fof(c_0_6,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ r1_tarski(X10,k1_relat_1(X12))
      | ~ r1_tarski(k9_relat_1(X12,X10),X11)
      | r1_tarski(X10,k10_relat_1(X12,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & r1_tarski(esk2_0,k1_relat_1(esk1_0))
    & k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9)
      | k10_relat_1(X9,X8) = k9_relat_1(k2_funct_1(X9),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk1_0,X2))
    | ~ r1_tarski(k9_relat_1(esk1_0,X1),X2)
    | ~ r1_tarski(X1,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v2_funct_1(X7)
      | r1_tarski(k10_relat_1(X7,k9_relat_1(X7,X6)),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

cnf(c_0_17,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,k10_relat_1(esk1_0,X1))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk1_0),X1) = k10_relat_1(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9]),c_0_10])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,k9_relat_1(esk1_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_9]),c_0_10])])).

cnf(c_0_27,negated_conjecture,
    ( k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.14/0.38  # and selection function PSelectSmallestOrientable.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t177_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 0.14/0.38  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.14/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.38  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 0.14/0.38  fof(t152_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2))), inference(assume_negation,[status(cth)],[t177_funct_1])).
% 0.14/0.38  fof(c_0_6, plain, ![X10, X11, X12]:(~v1_relat_1(X12)|~v1_funct_1(X12)|(~r1_tarski(X10,k1_relat_1(X12))|~r1_tarski(k9_relat_1(X12,X10),X11)|r1_tarski(X10,k10_relat_1(X12,X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v2_funct_1(esk1_0)&r1_tarski(esk2_0,k1_relat_1(esk1_0)))&k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0))!=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.38  cnf(c_0_8, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X8, X9]:(~v1_relat_1(X9)|~v1_funct_1(X9)|(~v2_funct_1(X9)|k10_relat_1(X9,X8)=k9_relat_1(k2_funct_1(X9),X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk1_0,X2))|~r1_tarski(k9_relat_1(esk1_0,X1),X2)|~r1_tarski(X1,k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  fof(c_0_16, plain, ![X6, X7]:(~v1_relat_1(X7)|~v1_funct_1(X7)|(~v2_funct_1(X7)|r1_tarski(k10_relat_1(X7,k9_relat_1(X7,X6)),X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).
% 0.14/0.38  cnf(c_0_17, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r1_tarski(esk2_0,k10_relat_1(esk1_0,X1))|~r1_tarski(k9_relat_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_21, plain, (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (k9_relat_1(k2_funct_1(esk1_0),X1)=k10_relat_1(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_9]), c_0_10])])).
% 0.14/0.38  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r1_tarski(esk2_0,k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,k9_relat_1(esk1_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_9]), c_0_10])])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0))!=esk2_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])]), c_0_27]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 29
% 0.14/0.38  # Proof object clause steps            : 18
% 0.14/0.38  # Proof object formula steps           : 11
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 10
% 0.14/0.38  # Proof object initial formulas used   : 5
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 13
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 5
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 11
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 11
% 0.14/0.38  # Processed clauses                    : 30
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 29
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 13
% 0.14/0.38  # ...of the previous two non-trivial   : 13
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 11
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
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
% 0.14/0.38  # Current number of processed clauses  : 16
% 0.14/0.38  #    Positive orientable unit clauses  : 8
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 7
% 0.14/0.38  # Current number of unprocessed clauses: 4
% 0.14/0.38  # ...number of literals in the above   : 10
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 11
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 8
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 2
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 2
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 8
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1017
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.027 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.031 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
