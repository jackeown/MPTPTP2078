%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  46 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 142 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t35_funct_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t70_funct_1])).

fof(c_0_7,plain,(
    ! [X4,X5,X6] :
      ( ( r2_hidden(X4,X5)
        | ~ r2_hidden(X4,k1_relat_1(k7_relat_1(X6,X5)))
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(X4,k1_relat_1(X6))
        | ~ r2_hidden(X4,k1_relat_1(k7_relat_1(X6,X5)))
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X4,X5)
        | ~ r2_hidden(X4,k1_relat_1(X6))
        | r2_hidden(X4,k1_relat_1(k7_relat_1(X6,X5)))
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))
    & k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ r2_hidden(X10,k1_relat_1(k5_relat_1(X12,X11)))
      | k1_funct_1(k5_relat_1(X12,X11),X10) = k1_funct_1(X11,k1_funct_1(X12,X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k7_relat_1(X8,X7) = k5_relat_1(k6_relat_1(X7),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_11,plain,(
    ! [X9] :
      ( v1_relat_1(k6_relat_1(X9))
      & v1_funct_1(k6_relat_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | k1_funct_1(k6_relat_1(X14),X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k1_funct_1(k6_relat_1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_22,plain,
    ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X2),X3)) = k1_funct_1(k7_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(k6_relat_1(esk2_0),esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_23]),c_0_24]),c_0_15])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:33:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.20/0.39  # and selection function SelectCQPrecWNTNp.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.038 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t70_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 0.20/0.39  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.20/0.39  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 0.20/0.39  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.39  fof(t35_funct_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k1_funct_1(k6_relat_1(X2),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 0.20/0.39  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t70_funct_1])).
% 0.20/0.39  fof(c_0_7, plain, ![X4, X5, X6]:(((r2_hidden(X4,X5)|~r2_hidden(X4,k1_relat_1(k7_relat_1(X6,X5)))|~v1_relat_1(X6))&(r2_hidden(X4,k1_relat_1(X6))|~r2_hidden(X4,k1_relat_1(k7_relat_1(X6,X5)))|~v1_relat_1(X6)))&(~r2_hidden(X4,X5)|~r2_hidden(X4,k1_relat_1(X6))|r2_hidden(X4,k1_relat_1(k7_relat_1(X6,X5)))|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.20/0.40  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))&k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.40  fof(c_0_9, plain, ![X10, X11, X12]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12)|(~r2_hidden(X10,k1_relat_1(k5_relat_1(X12,X11)))|k1_funct_1(k5_relat_1(X12,X11),X10)=k1_funct_1(X11,k1_funct_1(X12,X10))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.20/0.40  fof(c_0_10, plain, ![X7, X8]:(~v1_relat_1(X8)|k7_relat_1(X8,X7)=k5_relat_1(k6_relat_1(X7),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.40  fof(c_0_11, plain, ![X9]:(v1_relat_1(k6_relat_1(X9))&v1_funct_1(k6_relat_1(X9))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.40  fof(c_0_12, plain, ![X13, X14]:(~r2_hidden(X13,X14)|k1_funct_1(k6_relat_1(X14),X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).
% 0.20/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_16, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_17, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_18, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_19, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_20, plain, (k1_funct_1(k6_relat_1(X2),X1)=X1|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.20/0.40  cnf(c_0_22, plain, (k1_funct_1(X1,k1_funct_1(k6_relat_1(X2),X3))=k1_funct_1(k7_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (k1_funct_1(k6_relat_1(esk2_0),esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_14]), c_0_23]), c_0_24]), c_0_15])]), c_0_25]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 27
% 0.20/0.40  # Proof object clause steps            : 14
% 0.20/0.40  # Proof object formula steps           : 13
% 0.20/0.40  # Proof object conjectures             : 10
% 0.20/0.40  # Proof object clause conjectures      : 7
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 10
% 0.20/0.40  # Proof object initial formulas used   : 6
% 0.20/0.40  # Proof object generating inferences   : 4
% 0.20/0.40  # Proof object simplifying inferences  : 10
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 6
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 12
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 12
% 0.20/0.40  # Processed clauses                    : 39
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 0
% 0.20/0.40  # ...remaining for further processing  : 39
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 24
% 0.20/0.40  # ...of the previous two non-trivial   : 19
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 24
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 27
% 0.20/0.40  #    Positive orientable unit clauses  : 12
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 14
% 0.20/0.40  # Current number of unprocessed clauses: 4
% 0.20/0.40  # ...number of literals in the above   : 8
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 12
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 21
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 15
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 4
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 6
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 1374
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.043 s
% 0.20/0.40  # System time              : 0.002 s
% 0.20/0.40  # Total time               : 0.045 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
