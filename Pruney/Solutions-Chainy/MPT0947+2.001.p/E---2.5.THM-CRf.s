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
% DateTime   : Thu Dec  3 11:00:45 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   31 (  56 expanded)
%              Number of clauses        :   20 (  23 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 209 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X2,X3) )
               => r4_wellord1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t12_wellord2,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r4_wellord1(X1,k1_wellord2(X2))
                  & r4_wellord1(X1,k1_wellord2(X3)) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(t11_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ r4_wellord1(X6,X7)
      | ~ r4_wellord1(X7,X8)
      | r4_wellord1(X6,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).

fof(c_0_6,plain,(
    ! [X9] : v1_relat_1(k1_wellord2(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ! [X3] :
                ( v3_ordinal1(X3)
               => ( ( r4_wellord1(X1,k1_wellord2(X2))
                    & r4_wellord1(X1,k1_wellord2(X3)) )
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_wellord2])).

cnf(c_0_8,plain,
    ( r4_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & r4_wellord1(esk1_0,k1_wellord2(esk2_0))
    & r4_wellord1(esk1_0,k1_wellord2(esk3_0))
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ r4_wellord1(X4,X5)
      | r4_wellord1(X5,X4) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_12,plain,
    ( r4_wellord1(X1,k1_wellord2(X2))
    | ~ r4_wellord1(X3,k1_wellord2(X2))
    | ~ r4_wellord1(X1,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ~ v3_ordinal1(X10)
      | ~ v3_ordinal1(X11)
      | ~ r4_wellord1(k1_wellord2(X10),k1_wellord2(X11))
      | X10 = X11 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_wellord2])])])).

cnf(c_0_16,negated_conjecture,
    ( r4_wellord1(X1,k1_wellord2(X2))
    | ~ r4_wellord1(esk1_0,k1_wellord2(X2))
    | ~ r4_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r4_wellord1(k1_wellord2(X1),X2)
    | ~ r4_wellord1(X2,k1_wellord2(X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
    | ~ r4_wellord1(esk1_0,k1_wellord2(X2))
    | ~ r4_wellord1(k1_wellord2(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r4_wellord1(esk1_0,k1_wellord2(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r4_wellord1(k1_wellord2(X1),esk1_0)
    | ~ r4_wellord1(esk1_0,k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r4_wellord1(esk1_0,k1_wellord2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk3_0
    | ~ v3_ordinal1(X1)
    | ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( r4_wellord1(k1_wellord2(X1),k1_wellord2(esk3_0))
    | ~ r4_wellord1(k1_wellord2(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S086N
% 0.14/0.37  # and selection function SelectCQIArNp.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t52_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r4_wellord1(X1,X2)&r4_wellord1(X2,X3))=>r4_wellord1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_wellord1)).
% 0.14/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.14/0.37  fof(t12_wellord2, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r4_wellord1(X1,k1_wellord2(X2))&r4_wellord1(X1,k1_wellord2(X3)))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_wellord2)).
% 0.14/0.37  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.14/0.37  fof(t11_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.14/0.37  fof(c_0_5, plain, ![X6, X7, X8]:(~v1_relat_1(X6)|(~v1_relat_1(X7)|(~v1_relat_1(X8)|(~r4_wellord1(X6,X7)|~r4_wellord1(X7,X8)|r4_wellord1(X6,X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).
% 0.14/0.37  fof(c_0_6, plain, ![X9]:v1_relat_1(k1_wellord2(X9)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.14/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r4_wellord1(X1,k1_wellord2(X2))&r4_wellord1(X1,k1_wellord2(X3)))=>X2=X3))))), inference(assume_negation,[status(cth)],[t12_wellord2])).
% 0.14/0.37  cnf(c_0_8, plain, (r4_wellord1(X1,X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r4_wellord1(X1,X2)|~r4_wellord1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_9, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  fof(c_0_10, negated_conjecture, (v1_relat_1(esk1_0)&(v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&((r4_wellord1(esk1_0,k1_wellord2(esk2_0))&r4_wellord1(esk1_0,k1_wellord2(esk3_0)))&esk2_0!=esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.37  fof(c_0_11, plain, ![X4, X5]:(~v1_relat_1(X4)|(~v1_relat_1(X5)|(~r4_wellord1(X4,X5)|r4_wellord1(X5,X4)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.14/0.37  cnf(c_0_12, plain, (r4_wellord1(X1,k1_wellord2(X2))|~r4_wellord1(X3,k1_wellord2(X2))|~r4_wellord1(X1,X3)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_14, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  fof(c_0_15, plain, ![X10, X11]:(~v3_ordinal1(X10)|(~v3_ordinal1(X11)|(~r4_wellord1(k1_wellord2(X10),k1_wellord2(X11))|X10=X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_wellord2])])])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (r4_wellord1(X1,k1_wellord2(X2))|~r4_wellord1(esk1_0,k1_wellord2(X2))|~r4_wellord1(X1,esk1_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.37  cnf(c_0_17, plain, (r4_wellord1(k1_wellord2(X1),X2)|~r4_wellord1(X2,k1_wellord2(X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_14, c_0_9])).
% 0.14/0.37  cnf(c_0_18, plain, (X1=X2|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))|~r4_wellord1(esk1_0,k1_wellord2(X2))|~r4_wellord1(k1_wellord2(X1),esk1_0)), inference(spm,[status(thm)],[c_0_16, c_0_9])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (r4_wellord1(esk1_0,k1_wellord2(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (r4_wellord1(k1_wellord2(X1),esk1_0)|~r4_wellord1(esk1_0,k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_17, c_0_13])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (r4_wellord1(esk1_0,k1_wellord2(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (X1=esk3_0|~v3_ordinal1(X1)|~r4_wellord1(k1_wellord2(X1),k1_wellord2(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (r4_wellord1(k1_wellord2(X1),k1_wellord2(esk3_0))|~r4_wellord1(k1_wellord2(X1),esk1_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (r4_wellord1(k1_wellord2(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (~r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 31
% 0.14/0.37  # Proof object clause steps            : 20
% 0.14/0.37  # Proof object formula steps           : 11
% 0.14/0.37  # Proof object conjectures             : 17
% 0.14/0.37  # Proof object clause conjectures      : 14
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 10
% 0.14/0.37  # Proof object initial formulas used   : 5
% 0.14/0.37  # Proof object generating inferences   : 10
% 0.14/0.37  # Proof object simplifying inferences  : 2
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 5
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 10
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 10
% 0.14/0.37  # Processed clauses                    : 46
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 46
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 1
% 0.14/0.37  # Generated clauses                    : 36
% 0.14/0.37  # ...of the previous two non-trivial   : 30
% 0.14/0.37  # Contextual simplify-reflections      : 1
% 0.14/0.37  # Paramodulations                      : 36
% 0.14/0.37  # Factorizations                       : 0
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
% 0.14/0.37  # Current number of processed clauses  : 35
% 0.14/0.37  #    Positive orientable unit clauses  : 9
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 3
% 0.14/0.37  #    Non-unit-clauses                  : 23
% 0.14/0.37  # Current number of unprocessed clauses: 2
% 0.14/0.37  # ...number of literals in the above   : 5
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 11
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 85
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 71
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.37  # Unit Clause-clause subsumption calls : 1
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 1
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1416
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.030 s
% 0.14/0.37  # System time              : 0.001 s
% 0.14/0.37  # Total time               : 0.031 s
% 0.14/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
