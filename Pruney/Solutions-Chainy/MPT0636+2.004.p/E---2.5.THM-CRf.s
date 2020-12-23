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
% DateTime   : Thu Dec  3 10:53:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 124 expanded)
%              Number of clauses        :   18 (  43 expanded)
%              Number of leaves         :    4 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 553 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_funct_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ( r2_hidden(X6,k1_relat_1(X8))
        | ~ r2_hidden(X6,k1_relat_1(k5_relat_1(X8,X7)))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(k1_funct_1(X8,X6),k1_relat_1(X7))
        | ~ r2_hidden(X6,k1_relat_1(k5_relat_1(X8,X7)))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(X6,k1_relat_1(X8))
        | ~ r2_hidden(k1_funct_1(X8,X6),k1_relat_1(X7))
        | r2_hidden(X6,k1_relat_1(k5_relat_1(X8,X7)))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))
      | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) )
    & ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) )
    & ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)
      | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X5] :
      ( v1_relat_1(k6_relat_1(X5))
      & v1_funct_1(k6_relat_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_8,plain,(
    ! [X4] :
      ( k1_relat_1(k6_relat_1(X4)) = X4
      & k2_relat_1(k6_relat_1(X4)) = X4 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))
    | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_11]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)
    | r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12]),c_0_14])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_11]),c_0_13])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_22]),c_0_18]),c_0_12]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.038 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t40_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 0.13/0.39  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 0.13/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.39  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2))))), inference(assume_negation,[status(cth)],[t40_funct_1])).
% 0.13/0.39  fof(c_0_5, plain, ![X6, X7, X8]:(((r2_hidden(X6,k1_relat_1(X8))|~r2_hidden(X6,k1_relat_1(k5_relat_1(X8,X7)))|(~v1_relat_1(X8)|~v1_funct_1(X8))|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(r2_hidden(k1_funct_1(X8,X6),k1_relat_1(X7))|~r2_hidden(X6,k1_relat_1(k5_relat_1(X8,X7)))|(~v1_relat_1(X8)|~v1_funct_1(X8))|(~v1_relat_1(X7)|~v1_funct_1(X7))))&(~r2_hidden(X6,k1_relat_1(X8))|~r2_hidden(k1_funct_1(X8,X6),k1_relat_1(X7))|r2_hidden(X6,k1_relat_1(k5_relat_1(X8,X7)))|(~v1_relat_1(X8)|~v1_funct_1(X8))|(~v1_relat_1(X7)|~v1_funct_1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.13/0.39  fof(c_0_6, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))|(~r2_hidden(esk1_0,k1_relat_1(esk3_0))|~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)))&((r2_hidden(esk1_0,k1_relat_1(esk3_0))|r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))))&(r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)|r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.13/0.39  fof(c_0_7, plain, ![X5]:(v1_relat_1(k6_relat_1(X5))&v1_funct_1(k6_relat_1(X5))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.39  fof(c_0_8, plain, ![X4]:(k1_relat_1(k6_relat_1(X4))=X4&k2_relat_1(k6_relat_1(X4))=X4), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.39  cnf(c_0_9, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_10, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(esk3_0))|r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_11, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_13, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_15, plain, (r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_16, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))|~r2_hidden(esk1_0,k1_relat_1(esk3_0))|~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])])).
% 0.13/0.39  cnf(c_0_19, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_11]), c_0_13])])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)|r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))|~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18])])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_12]), c_0_14])])).
% 0.13/0.39  cnf(c_0_23, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])])).
% 0.13/0.39  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))|~r2_hidden(k1_funct_1(X2,X1),X3)|~r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_11]), c_0_13])])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_22]), c_0_18]), c_0_12]), c_0_14])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 27
% 0.13/0.39  # Proof object clause steps            : 18
% 0.13/0.39  # Proof object formula steps           : 9
% 0.13/0.39  # Proof object conjectures             : 13
% 0.13/0.39  # Proof object clause conjectures      : 10
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 11
% 0.13/0.39  # Proof object initial formulas used   : 4
% 0.13/0.39  # Proof object generating inferences   : 5
% 0.13/0.39  # Proof object simplifying inferences  : 23
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 4
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 12
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 12
% 0.13/0.39  # Processed clauses                    : 31
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 30
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 4
% 0.13/0.39  # Generated clauses                    : 15
% 0.13/0.39  # ...of the previous two non-trivial   : 9
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 15
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 14
% 0.13/0.39  #    Positive orientable unit clauses  : 8
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 5
% 0.13/0.39  # Current number of unprocessed clauses: 2
% 0.13/0.39  # ...number of literals in the above   : 18
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 16
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 6
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 13
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 2
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1289
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.008 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
