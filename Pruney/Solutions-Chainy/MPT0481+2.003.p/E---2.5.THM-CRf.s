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
% DateTime   : Thu Dec  3 10:49:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  58 expanded)
%              Number of clauses        :   16 (  23 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 197 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(t76_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(t75_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
      <=> ( r2_hidden(X2,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X15,X16),k5_relat_1(k6_relat_1(X17),X18))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(X15,X16),X18)
        | ~ r2_hidden(k4_tarski(X15,X16),k5_relat_1(k6_relat_1(X17),X18))
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X15,X16),X18)
        | r2_hidden(k4_tarski(X15,X16),k5_relat_1(k6_relat_1(X17),X18))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).

fof(c_0_7,plain,(
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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
          & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t76_relat_1])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(X20,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),k5_relat_1(X22,k6_relat_1(X21)))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(X19,X20),X22)
        | ~ r2_hidden(k4_tarski(X19,X20),k5_relat_1(X22,k6_relat_1(X21)))
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(X20,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),X22)
        | r2_hidden(k4_tarski(X19,X20),k5_relat_1(X22,k6_relat_1(X21)))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r1_tarski(k5_relat_1(esk4_0,k6_relat_1(esk3_0)),esk4_0)
      | ~ r1_tarski(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),esk2_2(k5_relat_1(k6_relat_1(X1),X2),X3)),X2)
    | r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk4_0,k6_relat_1(esk3_0)),esk4_0)
    | ~ r1_tarski(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),esk2_2(k5_relat_1(X1,k6_relat_1(X2)),X3)),X1)
    | r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)
    | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk4_0,k6_relat_1(esk3_0)),esk4_0)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_21,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | v1_relat_1(k5_relat_1(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_23,plain,(
    ! [X14] : v1_relat_1(k6_relat_1(X14)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))
    | ~ v1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_18])])).

cnf(c_0_25,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_26])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_26]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:09:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PI_PS_S5PRR_S032N
% 0.20/0.37  # and selection function SelectUnlessUniqMax.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t74_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 0.20/0.37  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.20/0.37  fof(t76_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.20/0.37  fof(t75_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))<=>(r2_hidden(X2,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_relat_1)).
% 0.20/0.37  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.37  fof(c_0_6, plain, ![X15, X16, X17, X18]:(((r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X15,X16),k5_relat_1(k6_relat_1(X17),X18))|~v1_relat_1(X18))&(r2_hidden(k4_tarski(X15,X16),X18)|~r2_hidden(k4_tarski(X15,X16),k5_relat_1(k6_relat_1(X17),X18))|~v1_relat_1(X18)))&(~r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X15,X16),X18)|r2_hidden(k4_tarski(X15,X16),k5_relat_1(k6_relat_1(X17),X18))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).
% 0.20/0.37  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(k4_tarski(X7,X8),X5)|r2_hidden(k4_tarski(X7,X8),X6))|~v1_relat_1(X5))&((r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X5)|r1_tarski(X5,X9)|~v1_relat_1(X5))&(~r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X9)|r1_tarski(X5,X9)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.20/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)))), inference(assume_negation,[status(cth)],[t76_relat_1])).
% 0.20/0.37  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  fof(c_0_11, plain, ![X19, X20, X21, X22]:(((r2_hidden(X20,X21)|~r2_hidden(k4_tarski(X19,X20),k5_relat_1(X22,k6_relat_1(X21)))|~v1_relat_1(X22))&(r2_hidden(k4_tarski(X19,X20),X22)|~r2_hidden(k4_tarski(X19,X20),k5_relat_1(X22,k6_relat_1(X21)))|~v1_relat_1(X22)))&(~r2_hidden(X20,X21)|~r2_hidden(k4_tarski(X19,X20),X22)|r2_hidden(k4_tarski(X19,X20),k5_relat_1(X22,k6_relat_1(X21)))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).
% 0.20/0.37  fof(c_0_12, negated_conjecture, (v1_relat_1(esk4_0)&(~r1_tarski(k5_relat_1(esk4_0,k6_relat_1(esk3_0)),esk4_0)|~r1_tarski(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.37  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),esk2_2(k5_relat_1(k6_relat_1(X1),X2),X3)),X2)|r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X3)|~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.37  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (~r1_tarski(k5_relat_1(esk4_0,k6_relat_1(esk3_0)),esk4_0)|~r1_tarski(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_17, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_19, plain, (r2_hidden(k4_tarski(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),esk2_2(k5_relat_1(X1,k6_relat_1(X2)),X3)),X1)|r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)|~v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_10])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (~r1_tarski(k5_relat_1(esk4_0,k6_relat_1(esk3_0)),esk4_0)|~v1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.20/0.37  cnf(c_0_21, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 0.20/0.37  fof(c_0_22, plain, ![X12, X13]:(~v1_relat_1(X12)|~v1_relat_1(X13)|v1_relat_1(k5_relat_1(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.37  fof(c_0_23, plain, ![X14]:v1_relat_1(k6_relat_1(X14)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (~v1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))|~v1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_18])])).
% 0.20/0.37  cnf(c_0_25, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.37  cnf(c_0_26, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (~v1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_18]), c_0_26])])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_26]), c_0_18])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 29
% 0.20/0.37  # Proof object clause steps            : 16
% 0.20/0.37  # Proof object formula steps           : 13
% 0.20/0.37  # Proof object conjectures             : 9
% 0.20/0.37  # Proof object clause conjectures      : 6
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 8
% 0.20/0.37  # Proof object initial formulas used   : 6
% 0.20/0.37  # Proof object generating inferences   : 8
% 0.20/0.37  # Proof object simplifying inferences  : 10
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 6
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 13
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 13
% 0.20/0.37  # Processed clauses                    : 53
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 4
% 0.20/0.37  # ...remaining for further processing  : 49
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 70
% 0.20/0.37  # ...of the previous two non-trivial   : 62
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 70
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
% 0.20/0.37  # Current number of processed clauses  : 36
% 0.20/0.37  #    Positive orientable unit clauses  : 2
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 33
% 0.20/0.37  # Current number of unprocessed clauses: 35
% 0.20/0.37  # ...number of literals in the above   : 163
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 13
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 240
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 86
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3060
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.029 s
% 0.20/0.37  # System time              : 0.005 s
% 0.20/0.37  # Total time               : 0.034 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
