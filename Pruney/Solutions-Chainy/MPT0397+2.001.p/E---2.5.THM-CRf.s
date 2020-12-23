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
% DateTime   : Thu Dec  3 10:47:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  62 expanded)
%              Number of clauses        :   17 (  24 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 192 expanded)
%              Number of equality atoms :   10 (  40 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d3_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X2)
            & ! [X4] :
                ~ ( r2_hidden(X4,X1)
                  & r1_tarski(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_setfam_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t19_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r2_setfam_1(X2,X1)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X12,X13,X15] :
      ( ( r2_hidden(esk1_3(X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | ~ r2_setfam_1(X8,X9) )
      & ( r1_tarski(esk1_3(X8,X9,X10),X10)
        | ~ r2_hidden(X10,X9)
        | ~ r2_setfam_1(X8,X9) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | r2_setfam_1(X12,X13) )
      & ( ~ r2_hidden(X15,X12)
        | ~ r1_tarski(X15,esk2_2(X12,X13))
        | r2_setfam_1(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_setfam_1])])])])])])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | r1_tarski(k1_setfam_1(X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_setfam_1(X2,X1)
       => ( X1 = k1_xboole_0
          | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t19_setfam_1])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( r2_hidden(esk3_2(X18,X19),X18)
        | X18 = k1_xboole_0
        | r1_tarski(X19,k1_setfam_1(X18)) )
      & ( ~ r1_tarski(X19,esk3_2(X18,X19))
        | X18 = k1_xboole_0
        | r1_tarski(X19,k1_setfam_1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_setfam_1(X4,X3)
    | ~ r1_tarski(X1,esk1_3(X4,X3,X2)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( r2_setfam_1(esk5_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & ~ r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk3_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(esk1_3(X3,X4,X2),X1)
    | ~ r2_hidden(X2,X4)
    | ~ r2_setfam_1(X3,X4) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r2_hidden(esk1_3(X3,X4,esk3_2(X1,k1_setfam_1(X2))),X2)
    | ~ r2_hidden(esk3_2(X1,k1_setfam_1(X2)),X4)
    | ~ r2_setfam_1(X3,X4) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,X2,esk3_2(esk4_0,k1_setfam_1(esk5_0))),esk5_0)
    | ~ r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),X2)
    | ~ r2_setfam_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_20]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,esk4_0,esk3_2(esk4_0,k1_setfam_1(esk5_0))),esk5_0)
    | ~ r2_setfam_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( r2_setfam_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk5_0,esk4_0,esk3_2(esk4_0,k1_setfam_1(esk5_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_22]),c_0_24])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.19/0.51  # and selection function SelectVGNonCR.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.026 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.51  fof(d3_setfam_1, axiom, ![X1, X2]:(r2_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X1)&r1_tarski(X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_setfam_1)).
% 0.19/0.51  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.19/0.51  fof(t19_setfam_1, conjecture, ![X1, X2]:(r2_setfam_1(X2,X1)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_setfam_1)).
% 0.19/0.51  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.19/0.51  fof(c_0_5, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.51  fof(c_0_6, plain, ![X8, X9, X10, X12, X13, X15]:(((r2_hidden(esk1_3(X8,X9,X10),X8)|~r2_hidden(X10,X9)|~r2_setfam_1(X8,X9))&(r1_tarski(esk1_3(X8,X9,X10),X10)|~r2_hidden(X10,X9)|~r2_setfam_1(X8,X9)))&((r2_hidden(esk2_2(X12,X13),X13)|r2_setfam_1(X12,X13))&(~r2_hidden(X15,X12)|~r1_tarski(X15,esk2_2(X12,X13))|r2_setfam_1(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_setfam_1])])])])])])).
% 0.19/0.51  cnf(c_0_7, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.51  cnf(c_0_8, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|~r2_hidden(X3,X2)|~r2_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  fof(c_0_9, plain, ![X16, X17]:(~r2_hidden(X16,X17)|r1_tarski(k1_setfam_1(X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.19/0.51  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(r2_setfam_1(X2,X1)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))))), inference(assume_negation,[status(cth)],[t19_setfam_1])).
% 0.19/0.51  fof(c_0_11, plain, ![X18, X19]:((r2_hidden(esk3_2(X18,X19),X18)|(X18=k1_xboole_0|r1_tarski(X19,k1_setfam_1(X18))))&(~r1_tarski(X19,esk3_2(X18,X19))|(X18=k1_xboole_0|r1_tarski(X19,k1_setfam_1(X18))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.19/0.51  cnf(c_0_12, plain, (r1_tarski(X1,X2)|~r2_hidden(X2,X3)|~r2_setfam_1(X4,X3)|~r1_tarski(X1,esk1_3(X4,X3,X2))), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.51  cnf(c_0_13, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.51  fof(c_0_14, negated_conjecture, (r2_setfam_1(esk5_0,esk4_0)&(esk4_0!=k1_xboole_0&~r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.51  cnf(c_0_15, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk3_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_16, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(esk1_3(X3,X4,X2),X1)|~r2_hidden(X2,X4)|~r2_setfam_1(X3,X4)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.51  cnf(c_0_17, negated_conjecture, (~r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_18, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r2_hidden(esk1_3(X3,X4,esk3_2(X1,k1_setfam_1(X2))),X2)|~r2_hidden(esk3_2(X1,k1_setfam_1(X2)),X4)|~r2_setfam_1(X3,X4)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.51  cnf(c_0_19, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_20, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_21, negated_conjecture, (~r2_hidden(esk1_3(X1,X2,esk3_2(esk4_0,k1_setfam_1(esk5_0))),esk5_0)|~r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),X2)|~r2_setfam_1(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.19/0.51  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_20]), c_0_19])).
% 0.19/0.51  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk1_3(X1,esk4_0,esk3_2(esk4_0,k1_setfam_1(esk5_0))),esk5_0)|~r2_setfam_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.51  cnf(c_0_24, negated_conjecture, (r2_setfam_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk1_3(esk5_0,esk4_0,esk3_2(esk4_0,k1_setfam_1(esk5_0))),esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.51  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|~r2_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_22]), c_0_24])]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 28
% 0.19/0.51  # Proof object clause steps            : 17
% 0.19/0.51  # Proof object formula steps           : 11
% 0.19/0.51  # Proof object conjectures             : 11
% 0.19/0.51  # Proof object clause conjectures      : 8
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 9
% 0.19/0.51  # Proof object initial formulas used   : 5
% 0.19/0.51  # Proof object generating inferences   : 8
% 0.19/0.51  # Proof object simplifying inferences  : 5
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 5
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 11
% 0.19/0.51  # Removed in clause preprocessing      : 0
% 0.19/0.51  # Initial clauses in saturation        : 11
% 0.19/0.51  # Processed clauses                    : 426
% 0.19/0.51  # ...of these trivial                  : 0
% 0.19/0.51  # ...subsumed                          : 75
% 0.19/0.51  # ...remaining for further processing  : 351
% 0.19/0.51  # Other redundant clauses eliminated   : 0
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 0
% 0.19/0.51  # Backward-rewritten                   : 0
% 0.19/0.51  # Generated clauses                    : 7442
% 0.19/0.51  # ...of the previous two non-trivial   : 7248
% 0.19/0.51  # Contextual simplify-reflections      : 0
% 0.19/0.51  # Paramodulations                      : 7442
% 0.19/0.51  # Factorizations                       : 0
% 0.19/0.51  # Equation resolutions                 : 0
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 340
% 0.19/0.51  #    Positive orientable unit clauses  : 2
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 5
% 0.19/0.51  #    Non-unit-clauses                  : 333
% 0.19/0.51  # Current number of unprocessed clauses: 6844
% 0.19/0.51  # ...number of literals in the above   : 53418
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 11
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 8870
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 2722
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 52
% 0.19/0.51  # Unit Clause-clause subsumption calls : 10
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 0
% 0.19/0.51  # BW rewrite match successes           : 0
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 205725
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.157 s
% 0.19/0.51  # System time              : 0.009 s
% 0.19/0.51  # Total time               : 0.166 s
% 0.19/0.51  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
