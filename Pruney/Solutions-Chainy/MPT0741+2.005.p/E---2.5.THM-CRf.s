%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 129 expanded)
%              Number of clauses        :   22 (  51 expanded)
%              Number of leaves         :    5 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 499 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_ordinal1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => ( v3_ordinal1(X2)
            & r1_tarski(X2,X1) ) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

fof(cc2_ordinal1,axiom,(
    ! [X1] :
      ( ( v1_ordinal1(X1)
        & v2_ordinal1(X1) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X1)
           => ( v3_ordinal1(X2)
              & r1_tarski(X2,X1) ) )
       => v3_ordinal1(X1) ) ),
    inference(assume_negation,[status(cth)],[t31_ordinal1])).

fof(c_0_6,negated_conjecture,(
    ! [X18] :
      ( ( v3_ordinal1(X18)
        | ~ r2_hidden(X18,esk4_0) )
      & ( r1_tarski(X18,esk4_0)
        | ~ r2_hidden(X18,esk4_0) )
      & ~ v3_ordinal1(esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_ordinal1(X5)
        | ~ r2_hidden(X6,X5)
        | r1_tarski(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_ordinal1(X7) )
      & ( ~ r1_tarski(esk1_1(X7),X7)
        | v1_ordinal1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v2_ordinal1(X9)
        | ~ r2_hidden(X10,X9)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X10,X11)
        | X10 = X11
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_1(X12),X12)
        | v2_ordinal1(X12) )
      & ( r2_hidden(esk3_1(X12),X12)
        | v2_ordinal1(X12) )
      & ( ~ r2_hidden(esk2_1(X12),esk3_1(X12))
        | v2_ordinal1(X12) )
      & ( esk2_1(X12) != esk3_1(X12)
        | v2_ordinal1(X12) )
      & ( ~ r2_hidden(esk3_1(X12),esk2_1(X12))
        | v2_ordinal1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

fof(c_0_9,plain,(
    ! [X4] :
      ( ~ v1_ordinal1(X4)
      | ~ v2_ordinal1(X4)
      | v3_ordinal1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_ordinal1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ v3_ordinal1(X15)
      | ~ v3_ordinal1(X16)
      | r2_hidden(X15,X16)
      | X15 = X16
      | r2_hidden(X16,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk3_1(esk4_0))
    | v2_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_ordinal1(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v3_ordinal1(esk3_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk2_1(esk4_0))
    | v2_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

cnf(c_0_25,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( esk3_1(esk4_0) = X1
    | r2_hidden(X1,esk3_1(esk4_0))
    | r2_hidden(esk3_1(esk4_0),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( v3_ordinal1(esk2_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_28,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk2_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( esk3_1(esk4_0) = esk2_1(esk4_0)
    | r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_20])).

cnf(c_0_30,plain,
    ( v2_ordinal1(X1)
    | esk2_1(X1) != esk3_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( esk3_1(esk4_0) = esk2_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.14/0.37  # and selection function SelectNewComplexAHPNS.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t31_ordinal1, conjecture, ![X1]:(![X2]:(r2_hidden(X2,X1)=>(v3_ordinal1(X2)&r1_tarski(X2,X1)))=>v3_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 0.14/0.37  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.14/0.37  fof(d3_ordinal1, axiom, ![X1]:(v2_ordinal1(X1)<=>![X2, X3]:~(((((r2_hidden(X2,X1)&r2_hidden(X3,X1))&~(r2_hidden(X2,X3)))&X2!=X3)&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_ordinal1)).
% 0.14/0.37  fof(cc2_ordinal1, axiom, ![X1]:((v1_ordinal1(X1)&v2_ordinal1(X1))=>v3_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_ordinal1)).
% 0.14/0.37  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.14/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(![X2]:(r2_hidden(X2,X1)=>(v3_ordinal1(X2)&r1_tarski(X2,X1)))=>v3_ordinal1(X1))), inference(assume_negation,[status(cth)],[t31_ordinal1])).
% 0.14/0.37  fof(c_0_6, negated_conjecture, ![X18]:(((v3_ordinal1(X18)|~r2_hidden(X18,esk4_0))&(r1_tarski(X18,esk4_0)|~r2_hidden(X18,esk4_0)))&~v3_ordinal1(esk4_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.14/0.37  fof(c_0_7, plain, ![X5, X6, X7]:((~v1_ordinal1(X5)|(~r2_hidden(X6,X5)|r1_tarski(X6,X5)))&((r2_hidden(esk1_1(X7),X7)|v1_ordinal1(X7))&(~r1_tarski(esk1_1(X7),X7)|v1_ordinal1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.14/0.37  fof(c_0_8, plain, ![X9, X10, X11, X12]:((~v2_ordinal1(X9)|(~r2_hidden(X10,X9)|~r2_hidden(X11,X9)|r2_hidden(X10,X11)|X10=X11|r2_hidden(X11,X10)))&(((((r2_hidden(esk2_1(X12),X12)|v2_ordinal1(X12))&(r2_hidden(esk3_1(X12),X12)|v2_ordinal1(X12)))&(~r2_hidden(esk2_1(X12),esk3_1(X12))|v2_ordinal1(X12)))&(esk2_1(X12)!=esk3_1(X12)|v2_ordinal1(X12)))&(~r2_hidden(esk3_1(X12),esk2_1(X12))|v2_ordinal1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).
% 0.14/0.37  fof(c_0_9, plain, ![X4]:(~v1_ordinal1(X4)|~v2_ordinal1(X4)|v3_ordinal1(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).
% 0.14/0.37  cnf(c_0_10, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_11, plain, (r2_hidden(esk1_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_12, plain, (v1_ordinal1(X1)|~r1_tarski(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_14, plain, (r2_hidden(esk3_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_15, plain, (v3_ordinal1(X1)|~v1_ordinal1(X1)|~v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (v1_ordinal1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (~v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  fof(c_0_18, plain, ![X15, X16]:(~v3_ordinal1(X15)|(~v3_ordinal1(X16)|(r2_hidden(X15,X16)|X15=X16|r2_hidden(X16,X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk3_1(esk4_0))|v2_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (~v2_ordinal1(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.14/0.37  cnf(c_0_21, plain, (r2_hidden(esk2_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (v3_ordinal1(esk3_1(esk4_0))), inference(sr,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (v3_ordinal1(esk2_1(esk4_0))|v2_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_21])).
% 0.14/0.37  cnf(c_0_25, plain, (v2_ordinal1(X1)|~r2_hidden(esk3_1(X1),esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (esk3_1(esk4_0)=X1|r2_hidden(X1,esk3_1(esk4_0))|r2_hidden(esk3_1(esk4_0),X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (v3_ordinal1(esk2_1(esk4_0))), inference(sr,[status(thm)],[c_0_24, c_0_20])).
% 0.14/0.37  cnf(c_0_28, plain, (v2_ordinal1(X1)|~r2_hidden(esk2_1(X1),esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (esk3_1(esk4_0)=esk2_1(esk4_0)|r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_20])).
% 0.14/0.37  cnf(c_0_30, plain, (v2_ordinal1(X1)|esk2_1(X1)!=esk3_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (esk3_1(esk4_0)=esk2_1(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_20])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_20]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 33
% 0.14/0.37  # Proof object clause steps            : 22
% 0.14/0.37  # Proof object formula steps           : 11
% 0.14/0.37  # Proof object conjectures             : 16
% 0.14/0.37  # Proof object clause conjectures      : 13
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 12
% 0.14/0.37  # Proof object initial formulas used   : 5
% 0.14/0.37  # Proof object generating inferences   : 8
% 0.14/0.37  # Proof object simplifying inferences  : 9
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 5
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 14
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 14
% 0.14/0.37  # Processed clauses                    : 29
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 29
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 5
% 0.14/0.37  # Generated clauses                    : 38
% 0.14/0.37  # ...of the previous two non-trivial   : 27
% 0.14/0.37  # Contextual simplify-reflections      : 1
% 0.14/0.37  # Paramodulations                      : 30
% 0.14/0.37  # Factorizations                       : 4
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 20
% 0.14/0.37  #    Positive orientable unit clauses  : 4
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 14
% 0.14/0.37  # Current number of unprocessed clauses: 11
% 0.14/0.37  # ...number of literals in the above   : 53
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 9
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 11
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 10
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.37  # Unit Clause-clause subsumption calls : 2
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 2
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1285
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.027 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.031 s
% 0.14/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
