%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  55 expanded)
%              Number of clauses        :   24 (  26 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 252 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(t179_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,plain,(
    ! [X12,X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(k4_tarski(X15,esk2_4(X12,X13,X14,X15)),X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk2_4(X12,X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X12)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(esk3_3(X12,X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk3_3(X12,X19,X20),X22),X12)
        | ~ r2_hidden(X22,X19)
        | X20 = k10_relat_1(X12,X19)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk3_3(X12,X19,X20),esk4_3(X12,X19,X20)),X12)
        | r2_hidden(esk3_3(X12,X19,X20),X20)
        | X20 = k10_relat_1(X12,X19)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk4_3(X12,X19,X20),X19)
        | r2_hidden(esk3_3(X12,X19,X20),X20)
        | X20 = k10_relat_1(X12,X19)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t179_relat_1])).

cnf(c_0_5,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k10_relat_1(esk6_0,esk5_0),k10_relat_1(esk7_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,esk2_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk2_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),X2),X1)
    | ~ r2_hidden(X2,k10_relat_1(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_4(esk6_0,X2,k10_relat_1(esk6_0,X2),X1)),esk6_0)
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk7_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk7_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk1_2(k10_relat_1(esk6_0,X1),X2)),X1)
    | r1_tarski(k10_relat_1(esk6_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk6_0,X1),X2),esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk1_2(k10_relat_1(esk6_0,X1),X2))),esk6_0)
    | r1_tarski(k10_relat_1(esk6_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk7_0,X2))
    | r1_tarski(k10_relat_1(esk6_0,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,esk2_4(esk6_0,X2,k10_relat_1(esk6_0,X2),esk1_2(k10_relat_1(esk6_0,X2),X3))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk6_0,X1),X2),esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk1_2(k10_relat_1(esk6_0,X1),X2))),esk7_0)
    | r1_tarski(k10_relat_1(esk6_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk6_0,X1),X2),k10_relat_1(esk7_0,X1))
    | r1_tarski(k10_relat_1(esk6_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk6_0,esk5_0),k10_relat_1(esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,X1),k10_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.19/0.51  # and selection function SelectCQIAr.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.027 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.51  fof(t179_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 0.19/0.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.51  fof(c_0_3, plain, ![X12, X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(k4_tarski(X15,esk2_4(X12,X13,X14,X15)),X12)|~r2_hidden(X15,X14)|X14!=k10_relat_1(X12,X13)|~v1_relat_1(X12))&(r2_hidden(esk2_4(X12,X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k10_relat_1(X12,X13)|~v1_relat_1(X12)))&(~r2_hidden(k4_tarski(X17,X18),X12)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k10_relat_1(X12,X13)|~v1_relat_1(X12)))&((~r2_hidden(esk3_3(X12,X19,X20),X20)|(~r2_hidden(k4_tarski(esk3_3(X12,X19,X20),X22),X12)|~r2_hidden(X22,X19))|X20=k10_relat_1(X12,X19)|~v1_relat_1(X12))&((r2_hidden(k4_tarski(esk3_3(X12,X19,X20),esk4_3(X12,X19,X20)),X12)|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k10_relat_1(X12,X19)|~v1_relat_1(X12))&(r2_hidden(esk4_3(X12,X19,X20),X19)|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k10_relat_1(X12,X19)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.51  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)))))), inference(assume_negation,[status(cth)],[t179_relat_1])).
% 0.19/0.51  cnf(c_0_5, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.19/0.51  fof(c_0_6, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&~r1_tarski(k10_relat_1(esk6_0,esk5_0),k10_relat_1(esk7_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.51  cnf(c_0_7, plain, (r2_hidden(k4_tarski(X1,esk2_4(X2,X3,X4,X1)),X2)|~r2_hidden(X1,X4)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.19/0.51  cnf(c_0_8, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.19/0.51  cnf(c_0_9, plain, (r2_hidden(esk2_4(X1,X2,k10_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_5])).
% 0.19/0.51  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  fof(c_0_11, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.51  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,esk2_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_7])).
% 0.19/0.51  cnf(c_0_13, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_8])).
% 0.19/0.51  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  cnf(c_0_15, negated_conjecture, (r2_hidden(esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),X2),X1)|~r2_hidden(X2,k10_relat_1(esk6_0,X1))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.51  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_18, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_4(esk6_0,X2,k10_relat_1(esk6_0,X2),X1)),esk6_0)|~r2_hidden(X1,k10_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_12, c_0_10])).
% 0.19/0.51  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk7_0,X2))|~r2_hidden(k4_tarski(X1,X3),esk7_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.51  cnf(c_0_21, negated_conjecture, (r2_hidden(esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk1_2(k10_relat_1(esk6_0,X1),X2)),X1)|r1_tarski(k10_relat_1(esk6_0,X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.51  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.51  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk6_0,X1),X2),esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk1_2(k10_relat_1(esk6_0,X1),X2))),esk6_0)|r1_tarski(k10_relat_1(esk6_0,X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.19/0.51  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk7_0,X2))|r1_tarski(k10_relat_1(esk6_0,X2),X3)|~r2_hidden(k4_tarski(X1,esk2_4(esk6_0,X2,k10_relat_1(esk6_0,X2),esk1_2(k10_relat_1(esk6_0,X2),X3))),esk7_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.51  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk6_0,X1),X2),esk2_4(esk6_0,X1,k10_relat_1(esk6_0,X1),esk1_2(k10_relat_1(esk6_0,X1),X2))),esk7_0)|r1_tarski(k10_relat_1(esk6_0,X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.51  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk6_0,X1),X2),k10_relat_1(esk7_0,X1))|r1_tarski(k10_relat_1(esk6_0,X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.51  cnf(c_0_28, negated_conjecture, (~r1_tarski(k10_relat_1(esk6_0,esk5_0),k10_relat_1(esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  cnf(c_0_29, negated_conjecture, (r1_tarski(k10_relat_1(esk6_0,X1),k10_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.51  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 31
% 0.19/0.51  # Proof object clause steps            : 24
% 0.19/0.51  # Proof object formula steps           : 7
% 0.19/0.51  # Proof object conjectures             : 18
% 0.19/0.51  # Proof object clause conjectures      : 15
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 10
% 0.19/0.51  # Proof object initial formulas used   : 3
% 0.19/0.51  # Proof object generating inferences   : 10
% 0.19/0.51  # Proof object simplifying inferences  : 5
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 3
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 13
% 0.19/0.51  # Removed in clause preprocessing      : 0
% 0.19/0.51  # Initial clauses in saturation        : 13
% 0.19/0.51  # Processed clauses                    : 691
% 0.19/0.51  # ...of these trivial                  : 0
% 0.19/0.51  # ...subsumed                          : 80
% 0.19/0.51  # ...remaining for further processing  : 611
% 0.19/0.51  # Other redundant clauses eliminated   : 3
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 4
% 0.19/0.51  # Backward-rewritten                   : 1
% 0.19/0.51  # Generated clauses                    : 2356
% 0.19/0.51  # ...of the previous two non-trivial   : 2349
% 0.19/0.51  # Contextual simplify-reflections      : 0
% 0.19/0.51  # Paramodulations                      : 2331
% 0.19/0.51  # Factorizations                       : 22
% 0.19/0.51  # Equation resolutions                 : 3
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
% 0.19/0.51  # Current number of processed clauses  : 590
% 0.19/0.51  #    Positive orientable unit clauses  : 9
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 0
% 0.19/0.51  #    Non-unit-clauses                  : 581
% 0.19/0.51  # Current number of unprocessed clauses: 1684
% 0.19/0.51  # ...number of literals in the above   : 6734
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 18
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 19219
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 8113
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 84
% 0.19/0.51  # Unit Clause-clause subsumption calls : 182
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 6
% 0.19/0.51  # BW rewrite match successes           : 1
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 86718
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.164 s
% 0.19/0.51  # System time              : 0.006 s
% 0.19/0.51  # Total time               : 0.170 s
% 0.19/0.51  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
