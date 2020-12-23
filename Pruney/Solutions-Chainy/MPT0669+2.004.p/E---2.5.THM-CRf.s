%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:20 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 ( 102 expanded)
%              Number of clauses        :   17 (  37 expanded)
%              Number of leaves         :    3 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 476 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(t86_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(c_0_3,plain,(
    ! [X6,X7,X8] :
      ( ( r2_hidden(X6,k1_relat_1(X8))
        | ~ r2_hidden(X6,k1_relat_1(k5_relat_1(X8,k6_relat_1(X7))))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(k1_funct_1(X8,X6),X7)
        | ~ r2_hidden(X6,k1_relat_1(k5_relat_1(X8,k6_relat_1(X7))))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(X6,k1_relat_1(X8))
        | ~ r2_hidden(k1_funct_1(X8,X6),X7)
        | r2_hidden(X6,k1_relat_1(k5_relat_1(X8,k6_relat_1(X7))))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).

fof(c_0_4,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | k8_relat_1(X4,X5) = k5_relat_1(X5,k6_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_funct_1])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ( ~ r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))
      | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) )
    & ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))) )
    & ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)
      | r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))
    | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)
    | r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11]),c_0_12])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X3,X1),X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19]),c_0_15]),c_0_11]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t40_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 0.13/0.37  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.13/0.37  fof(t86_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 0.13/0.37  fof(c_0_3, plain, ![X6, X7, X8]:(((r2_hidden(X6,k1_relat_1(X8))|~r2_hidden(X6,k1_relat_1(k5_relat_1(X8,k6_relat_1(X7))))|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(r2_hidden(k1_funct_1(X8,X6),X7)|~r2_hidden(X6,k1_relat_1(k5_relat_1(X8,k6_relat_1(X7))))|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(~r2_hidden(X6,k1_relat_1(X8))|~r2_hidden(k1_funct_1(X8,X6),X7)|r2_hidden(X6,k1_relat_1(k5_relat_1(X8,k6_relat_1(X7))))|(~v1_relat_1(X8)|~v1_funct_1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).
% 0.13/0.37  fof(c_0_4, plain, ![X4, X5]:(~v1_relat_1(X5)|k8_relat_1(X4,X5)=k5_relat_1(X5,k6_relat_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2))))), inference(assume_negation,[status(cth)],[t86_funct_1])).
% 0.13/0.37  cnf(c_0_6, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_7, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))|(~r2_hidden(esk1_0,k1_relat_1(esk3_0))|~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)))&((r2_hidden(esk1_0,k1_relat_1(esk3_0))|r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))))&(r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)|r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(esk3_0))|r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))|~r2_hidden(esk1_0,k1_relat_1(esk3_0))|~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])])).
% 0.13/0.37  cnf(c_0_16, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_7])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)|r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))|~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15])])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11]), c_0_12])])).
% 0.13/0.37  cnf(c_0_20, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])])).
% 0.13/0.37  cnf(c_0_22, plain, (r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))|~r2_hidden(k1_funct_1(X3,X1),X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_funct_1(X3)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_20, c_0_7])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19]), c_0_15]), c_0_11]), c_0_12])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 24
% 0.13/0.37  # Proof object clause steps            : 17
% 0.13/0.37  # Proof object formula steps           : 7
% 0.13/0.37  # Proof object conjectures             : 13
% 0.13/0.37  # Proof object clause conjectures      : 10
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 9
% 0.13/0.37  # Proof object initial formulas used   : 3
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 15
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 3
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 9
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 9
% 0.13/0.37  # Processed clauses                    : 25
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 25
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 4
% 0.13/0.37  # Generated clauses                    : 14
% 0.13/0.37  # ...of the previous two non-trivial   : 8
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 14
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 12
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 7
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 13
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 34
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1046
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
