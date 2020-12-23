%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  48 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 234 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & ! [X4] :
                  ~ ( r2_hidden(X4,k1_relat_1(X2))
                    & X3 = k1_funct_1(X2,X4) ) )
       => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & ! [X4] :
                    ~ ( r2_hidden(X4,k1_relat_1(X2))
                      & X3 = k1_funct_1(X2,X4) ) )
         => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t19_funct_1])).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X15,X16,X17,X19] :
      ( ( r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X11))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | r2_hidden(X15,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk3_2(X11,X17),X17)
        | ~ r2_hidden(X19,k1_relat_1(X11))
        | esk3_2(X11,X17) != k1_funct_1(X11,X19)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_2(X11,X17),k1_relat_1(X11))
        | r2_hidden(esk3_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk3_2(X11,X17) = k1_funct_1(X11,esk4_2(X11,X17))
        | r2_hidden(esk3_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X23] :
      ( v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & ( r2_hidden(esk7_1(X23),k1_relat_1(esk6_0))
        | ~ r2_hidden(X23,esk5_0) )
      & ( X23 = k1_funct_1(esk6_0,esk7_1(X23))
        | ~ r2_hidden(X23,esk5_0) )
      & ~ r1_tarski(esk5_0,k2_relat_1(esk6_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k2_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk7_1(X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( X1 = k1_funct_1(esk6_0,esk7_1(X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk7_1(esk1_2(esk5_0,k2_relat_1(esk6_0))),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k1_funct_1(esk6_0,esk7_1(esk1_2(esk5_0,k2_relat_1(esk6_0)))) = esk1_2(esk5_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.20/0.39  # and selection function SelectDivPreferIntoLits.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.044 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t19_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,k1_relat_1(X2))&X3=k1_funct_1(X2,X4)))))=>r1_tarski(X1,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_funct_1)).
% 0.20/0.39  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(c_0_3, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,k1_relat_1(X2))&X3=k1_funct_1(X2,X4)))))=>r1_tarski(X1,k2_relat_1(X2))))), inference(assume_negation,[status(cth)],[t19_funct_1])).
% 0.20/0.39  fof(c_0_4, plain, ![X11, X12, X13, X15, X16, X17, X19]:((((r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X11))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(X13=k1_funct_1(X11,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(X16,k1_relat_1(X11))|X15!=k1_funct_1(X11,X16)|r2_hidden(X15,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((~r2_hidden(esk3_2(X11,X17),X17)|(~r2_hidden(X19,k1_relat_1(X11))|esk3_2(X11,X17)!=k1_funct_1(X11,X19))|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&((r2_hidden(esk4_2(X11,X17),k1_relat_1(X11))|r2_hidden(esk3_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(esk3_2(X11,X17)=k1_funct_1(X11,esk4_2(X11,X17))|r2_hidden(esk3_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.39  fof(c_0_5, negated_conjecture, ![X23]:((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(((r2_hidden(esk7_1(X23),k1_relat_1(esk6_0))|~r2_hidden(X23,esk5_0))&(X23=k1_funct_1(esk6_0,esk7_1(X23))|~r2_hidden(X23,esk5_0)))&~r1_tarski(esk5_0,k2_relat_1(esk6_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).
% 0.20/0.39  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_7, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.39  cnf(c_0_8, negated_conjecture, (~r1_tarski(esk5_0,k2_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.39  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_10, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).
% 0.20/0.39  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.39  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (r2_hidden(esk7_1(X1),k1_relat_1(esk6_0))|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (X1=k1_funct_1(esk6_0,esk7_1(X1))|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),k2_relat_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (r2_hidden(esk7_1(esk1_2(esk5_0,k2_relat_1(esk6_0))),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (k1_funct_1(esk6_0,esk7_1(esk1_2(esk5_0,k2_relat_1(esk6_0))))=esk1_2(esk5_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.20/0.39  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_8]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 22
% 0.20/0.39  # Proof object clause steps            : 15
% 0.20/0.39  # Proof object formula steps           : 7
% 0.20/0.39  # Proof object conjectures             : 14
% 0.20/0.39  # Proof object clause conjectures      : 11
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 8
% 0.20/0.39  # Proof object initial formulas used   : 3
% 0.20/0.39  # Proof object generating inferences   : 6
% 0.20/0.39  # Proof object simplifying inferences  : 6
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 3
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 14
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 14
% 0.20/0.39  # Processed clauses                    : 35
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 35
% 0.20/0.39  # Other redundant clauses eliminated   : 4
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 16
% 0.20/0.39  # ...of the previous two non-trivial   : 15
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 13
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 4
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
% 0.20/0.39  # Current number of processed clauses  : 18
% 0.20/0.39  #    Positive orientable unit clauses  : 6
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 11
% 0.20/0.39  # Current number of unprocessed clauses: 6
% 0.20/0.39  # ...number of literals in the above   : 21
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 14
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 35
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 14
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.39  # Unit Clause-clause subsumption calls : 1
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1447
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.043 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.050 s
% 0.20/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
