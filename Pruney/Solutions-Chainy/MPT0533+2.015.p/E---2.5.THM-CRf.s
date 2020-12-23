%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  50 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 209 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(t131_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t133_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(t132_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(k4_tarski(X7,X8),X5)
        | r2_hidden(k4_tarski(X7,X8),X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X5)
        | r1_tarski(X5,X9)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X9)
        | r1_tarski(X5,X9)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X1,X4)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_8])).

fof(c_0_11,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(k8_relat_1(X14,X16),k8_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t131_relat_1])])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k8_relat_1(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t133_relat_1])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(k8_relat_1(X2,X1),k8_relat_1(X3,X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k8_relat_1(X17,X18),k8_relat_1(X17,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_relat_1])])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k8_relat_1(X2,X3))
    | ~ r1_tarski(X1,k8_relat_1(X4,X3))
    | ~ r1_tarski(X4,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(k8_relat_1(X3,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X3,X4))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X2,X4)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S033I
% 0.20/0.37  # and selection function PSelectUnlessUniqMax.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.20/0.37  fof(t131_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 0.20/0.37  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.20/0.37  fof(t133_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 0.20/0.37  fof(t132_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 0.20/0.37  fof(c_0_5, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(k4_tarski(X7,X8),X5)|r2_hidden(k4_tarski(X7,X8),X6))|~v1_relat_1(X5))&((r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X5)|r1_tarski(X5,X9)|~v1_relat_1(X5))&(~r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X9)|r1_tarski(X5,X9)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.20/0.37  cnf(c_0_6, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_7, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_8, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.20/0.37  cnf(c_0_9, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X3)|r1_tarski(X1,X2)|~r1_tarski(X4,X3)|~r1_tarski(X1,X4)|~v1_relat_1(X4)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_6, c_0_8])).
% 0.20/0.37  fof(c_0_11, plain, ![X14, X15, X16]:(~v1_relat_1(X16)|(~r1_tarski(X14,X15)|r1_tarski(k8_relat_1(X14,X16),k8_relat_1(X15,X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t131_relat_1])])).
% 0.20/0.37  fof(c_0_12, plain, ![X12, X13]:(~v1_relat_1(X13)|v1_relat_1(k8_relat_1(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.20/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)))))), inference(assume_negation,[status(cth)],[t133_relat_1])).
% 0.20/0.37  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.37  cnf(c_0_15, plain, (r1_tarski(k8_relat_1(X2,X1),k8_relat_1(X3,X1))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_16, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  fof(c_0_17, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(X18,X19)|r1_tarski(k8_relat_1(X17,X18),k8_relat_1(X17,X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_relat_1])])])).
% 0.20/0.37  fof(c_0_18, negated_conjecture, (v1_relat_1(esk5_0)&(v1_relat_1(esk6_0)&((r1_tarski(esk5_0,esk6_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.37  cnf(c_0_19, plain, (r1_tarski(X1,k8_relat_1(X2,X3))|~r1_tarski(X1,k8_relat_1(X4,X3))|~r1_tarski(X4,X2)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.20/0.37  cnf(c_0_20, plain, (r1_tarski(k8_relat_1(X3,X1),k8_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (~r1_tarski(k8_relat_1(esk3_0,esk5_0),k8_relat_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_22, plain, (r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X3,X4))|~r1_tarski(X1,X3)|~r1_tarski(X2,X4)|~v1_relat_1(X4)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_16])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 28
% 0.20/0.37  # Proof object clause steps            : 17
% 0.20/0.37  # Proof object formula steps           : 11
% 0.20/0.37  # Proof object conjectures             : 9
% 0.20/0.37  # Proof object clause conjectures      : 6
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 5
% 0.20/0.37  # Proof object generating inferences   : 6
% 0.20/0.37  # Proof object simplifying inferences  : 7
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 5
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 11
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 11
% 0.20/0.37  # Processed clauses                    : 41
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 5
% 0.20/0.37  # ...remaining for further processing  : 36
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 33
% 0.20/0.37  # ...of the previous two non-trivial   : 29
% 0.20/0.37  # Contextual simplify-reflections      : 3
% 0.20/0.37  # Paramodulations                      : 33
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 25
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 20
% 0.20/0.37  # Current number of unprocessed clauses: 6
% 0.20/0.37  # ...number of literals in the above   : 45
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 11
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 302
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 125
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1651
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.030 s
% 0.20/0.37  # System time              : 0.003 s
% 0.20/0.37  # Total time               : 0.033 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
