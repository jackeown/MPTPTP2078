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
% DateTime   : Thu Dec  3 10:49:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  57 expanded)
%              Number of clauses        :   16 (  25 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 205 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k4_tarski(X3,X3),X2) )
       => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r2_hidden(k4_tarski(X3,X3),X2) )
         => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t73_relat_1])).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk3_2(X13,X17),esk4_2(X13,X17)),X13)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X13,X17),esk4_2(X13,X17)),X17)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X20] : v1_relat_1(k6_relat_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X5)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( X7 = X8
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X9,X5)
        | X9 != X10
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(esk1_2(X5,X6),X5)
        | esk1_2(X5,X6) != esk2_2(X5,X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( esk1_2(X5,X6) = esk2_2(X5,X6)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X23] :
      ( v1_relat_1(esk6_0)
      & ( ~ r2_hidden(X23,esk5_0)
        | r2_hidden(k4_tarski(X23,X23),esk6_0) )
      & ~ r1_tarski(k6_relat_1(esk5_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k6_relat_1(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | r2_hidden(k4_tarski(esk3_2(k6_relat_1(X1),X2),esk4_2(k6_relat_1(X1),X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_10])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k6_relat_1(esk5_0),esk6_0),esk4_2(k6_relat_1(esk5_0),esk6_0)),k6_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_10])])).

cnf(c_0_19,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ r2_hidden(k4_tarski(esk3_2(k6_relat_1(X1),X2),esk4_2(k6_relat_1(X1),X2)),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( esk4_2(k6_relat_1(esk5_0),esk6_0) = esk3_2(k6_relat_1(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_2(k6_relat_1(esk5_0),esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_2(k6_relat_1(esk5_0),esk6_0),esk3_2(k6_relat_1(esk5_0),esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:43:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.13/0.37  # and selection function SelectSmallestOrientable.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t73_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(![X3]:(r2_hidden(X3,X1)=>r2_hidden(k4_tarski(X3,X3),X2))=>r1_tarski(k6_relat_1(X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 0.13/0.37  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.13/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.37  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.13/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(![X3]:(r2_hidden(X3,X1)=>r2_hidden(k4_tarski(X3,X3),X2))=>r1_tarski(k6_relat_1(X1),X2)))), inference(assume_negation,[status(cth)],[t73_relat_1])).
% 0.13/0.37  fof(c_0_5, plain, ![X13, X14, X15, X16, X17]:((~r1_tarski(X13,X14)|(~r2_hidden(k4_tarski(X15,X16),X13)|r2_hidden(k4_tarski(X15,X16),X14))|~v1_relat_1(X13))&((r2_hidden(k4_tarski(esk3_2(X13,X17),esk4_2(X13,X17)),X13)|r1_tarski(X13,X17)|~v1_relat_1(X13))&(~r2_hidden(k4_tarski(esk3_2(X13,X17),esk4_2(X13,X17)),X17)|r1_tarski(X13,X17)|~v1_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X20]:v1_relat_1(k6_relat_1(X20)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.37  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10]:((((r2_hidden(X7,X5)|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6))&(X7=X8|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&(~r2_hidden(X9,X5)|X9!=X10|r2_hidden(k4_tarski(X9,X10),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|(~r2_hidden(esk1_2(X5,X6),X5)|esk1_2(X5,X6)!=esk2_2(X5,X6))|X6=k6_relat_1(X5)|~v1_relat_1(X6))&((r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))&(esk1_2(X5,X6)=esk2_2(X5,X6)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ![X23]:(v1_relat_1(esk6_0)&((~r2_hidden(X23,esk5_0)|r2_hidden(k4_tarski(X23,X23),esk6_0))&~r1_tarski(k6_relat_1(esk5_0),esk6_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_10, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_11, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X2),X3)|X3!=k6_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (~r1_tarski(k6_relat_1(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, plain, (r1_tarski(k6_relat_1(X1),X2)|r2_hidden(k4_tarski(esk3_2(k6_relat_1(X1),X2),esk4_2(k6_relat_1(X1),X2)),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_16, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_10])])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(k6_relat_1(esk5_0),esk6_0),esk4_2(k6_relat_1(esk5_0),esk6_0)),k6_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_10])])).
% 0.13/0.37  cnf(c_0_19, plain, (r1_tarski(k6_relat_1(X1),X2)|~r2_hidden(k4_tarski(esk3_2(k6_relat_1(X1),X2),esk4_2(k6_relat_1(X1),X2)),X2)), inference(spm,[status(thm)],[c_0_15, c_0_10])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (esk4_2(k6_relat_1(esk5_0),esk6_0)=esk3_2(k6_relat_1(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(X1,X1),esk6_0)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_2(k6_relat_1(esk5_0),esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (~r2_hidden(k4_tarski(esk3_2(k6_relat_1(esk5_0),esk6_0),esk3_2(k6_relat_1(esk5_0),esk6_0)),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_12])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 25
% 0.13/0.37  # Proof object clause steps            : 16
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 10
% 0.13/0.37  # Proof object clause conjectures      : 7
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 7
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 8
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 13
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 13
% 0.13/0.37  # Processed clauses                    : 54
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 3
% 0.13/0.37  # ...remaining for further processing  : 50
% 0.13/0.37  # Other redundant clauses eliminated   : 4
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 2
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 94
% 0.13/0.37  # ...of the previous two non-trivial   : 92
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 91
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 4
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
% 0.13/0.37  # Current number of processed clauses  : 31
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 25
% 0.13/0.37  # Current number of unprocessed clauses: 63
% 0.13/0.37  # ...number of literals in the above   : 232
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 16
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 151
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 78
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.37  # Unit Clause-clause subsumption calls : 23
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3515
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
