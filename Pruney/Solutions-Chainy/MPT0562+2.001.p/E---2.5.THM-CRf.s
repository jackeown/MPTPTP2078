%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  70 expanded)
%              Number of clauses        :   17 (  28 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 458 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t166_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k10_relat_1(X3,X2))
        <=> ? [X4] :
              ( r2_hidden(X4,k2_relat_1(X3))
              & r2_hidden(k4_tarski(X1,X4),X3)
              & r2_hidden(X4,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t166_relat_1])).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(X9,esk1_4(X6,X7,X8,X9)),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(esk2_3(X6,X13,X14),X16),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk2_3(X6,X13,X14),esk3_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X32] :
      ( v1_relat_1(esk9_0)
      & ( ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
        | ~ r2_hidden(X32,k2_relat_1(esk9_0))
        | ~ r2_hidden(k4_tarski(esk7_0,X32),esk9_0)
        | ~ r2_hidden(X32,esk8_0) )
      & ( r2_hidden(esk10_0,k2_relat_1(esk9_0))
        | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) )
      & ( r2_hidden(k4_tarski(esk7_0,esk10_0),esk9_0)
        | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) )
      & ( r2_hidden(esk10_0,esk8_0)
        | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk10_0),esk9_0)
    | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(k4_tarski(esk7_0,X1),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | r2_hidden(esk7_0,X1)
    | X1 != k10_relat_1(esk9_0,X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_12,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,X2)
    | ~ r2_hidden(esk1_4(esk9_0,X2,X1,esk7_0),k2_relat_1(esk9_0))
    | ~ r2_hidden(esk1_4(esk9_0,X2,X1,esk7_0),esk8_0)
    | ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_8])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | r2_hidden(esk7_0,k10_relat_1(esk9_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0)
    | r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(esk4_3(X18,X19,X20),X20),X18)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X22),X18)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(X27,esk5_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) )
      & ( r2_hidden(esk5_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk6_2(X24,X25),esk5_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,esk8_0)
    | ~ r2_hidden(esk1_4(esk9_0,esk8_0,X1,esk7_0),k2_relat_1(esk9_0))
    | ~ r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,esk8_0)
    | ~ r2_hidden(esk1_4(esk9_0,esk8_0,X1,esk7_0),k2_relat_1(esk9_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X5)
    | X3 != k10_relat_1(X1,X2)
    | X5 != k2_relat_1(X1)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( X1 != k10_relat_1(esk9_0,esk8_0)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_8])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_22,c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.038 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t166_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.13/0.39  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.13/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.13/0.39  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2))))), inference(assume_negation,[status(cth)],[t166_relat_1])).
% 0.13/0.39  fof(c_0_4, plain, ![X6, X7, X8, X9, X11, X12, X13, X14, X16]:((((r2_hidden(k4_tarski(X9,esk1_4(X6,X7,X8,X9)),X6)|~r2_hidden(X9,X8)|X8!=k10_relat_1(X6,X7)|~v1_relat_1(X6))&(r2_hidden(esk1_4(X6,X7,X8,X9),X7)|~r2_hidden(X9,X8)|X8!=k10_relat_1(X6,X7)|~v1_relat_1(X6)))&(~r2_hidden(k4_tarski(X11,X12),X6)|~r2_hidden(X12,X7)|r2_hidden(X11,X8)|X8!=k10_relat_1(X6,X7)|~v1_relat_1(X6)))&((~r2_hidden(esk2_3(X6,X13,X14),X14)|(~r2_hidden(k4_tarski(esk2_3(X6,X13,X14),X16),X6)|~r2_hidden(X16,X13))|X14=k10_relat_1(X6,X13)|~v1_relat_1(X6))&((r2_hidden(k4_tarski(esk2_3(X6,X13,X14),esk3_3(X6,X13,X14)),X6)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k10_relat_1(X6,X13)|~v1_relat_1(X6))&(r2_hidden(esk3_3(X6,X13,X14),X13)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k10_relat_1(X6,X13)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.13/0.39  fof(c_0_5, negated_conjecture, ![X32]:(v1_relat_1(esk9_0)&((~r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))|(~r2_hidden(X32,k2_relat_1(esk9_0))|~r2_hidden(k4_tarski(esk7_0,X32),esk9_0)|~r2_hidden(X32,esk8_0)))&(((r2_hidden(esk10_0,k2_relat_1(esk9_0))|r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)))&(r2_hidden(k4_tarski(esk7_0,esk10_0),esk9_0)|r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))))&(r2_hidden(esk10_0,esk8_0)|r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).
% 0.13/0.39  cnf(c_0_6, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_7, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk10_0),esk9_0)|r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_8, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_9, negated_conjecture, (~r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))|~r2_hidden(X1,k2_relat_1(esk9_0))|~r2_hidden(k4_tarski(esk7_0,X1),esk9_0)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)|~r2_hidden(X1,X4)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_11, negated_conjecture, (r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))|r2_hidden(esk7_0,X1)|X1!=k10_relat_1(esk9_0,X2)|~r2_hidden(esk10_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])])).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (X1!=k10_relat_1(esk9_0,X2)|~r2_hidden(esk1_4(esk9_0,X2,X1,esk7_0),k2_relat_1(esk9_0))|~r2_hidden(esk1_4(esk9_0,X2,X1,esk7_0),esk8_0)|~r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_8])])).
% 0.13/0.39  cnf(c_0_13, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))|r2_hidden(esk7_0,k10_relat_1(esk9_0,X1))|~r2_hidden(esk10_0,X1)), inference(er,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (r2_hidden(esk10_0,esk8_0)|r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  fof(c_0_16, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(esk4_3(X18,X19,X20),X20),X18)|X19!=k2_relat_1(X18))&(~r2_hidden(k4_tarski(X23,X22),X18)|r2_hidden(X22,X19)|X19!=k2_relat_1(X18)))&((~r2_hidden(esk5_2(X24,X25),X25)|~r2_hidden(k4_tarski(X27,esk5_2(X24,X25)),X24)|X25=k2_relat_1(X24))&(r2_hidden(esk5_2(X24,X25),X25)|r2_hidden(k4_tarski(esk6_2(X24,X25),esk5_2(X24,X25)),X24)|X25=k2_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (X1!=k10_relat_1(esk9_0,esk8_0)|~r2_hidden(esk1_4(esk9_0,esk8_0,X1,esk7_0),k2_relat_1(esk9_0))|~r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_8])])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (r2_hidden(esk7_0,k10_relat_1(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.39  cnf(c_0_19, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (X1!=k10_relat_1(esk9_0,esk8_0)|~r2_hidden(esk1_4(esk9_0,esk8_0,X1,esk7_0),k2_relat_1(esk9_0))|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18])])).
% 0.13/0.39  cnf(c_0_21, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X5)|X3!=k10_relat_1(X1,X2)|X5!=k2_relat_1(X1)|~r2_hidden(X4,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_10])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (X1!=k10_relat_1(esk9_0,esk8_0)|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_8])])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_22, c_0_18]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 24
% 0.13/0.39  # Proof object clause steps            : 17
% 0.13/0.39  # Proof object formula steps           : 7
% 0.13/0.39  # Proof object conjectures             : 15
% 0.13/0.39  # Proof object clause conjectures      : 12
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 8
% 0.13/0.39  # Proof object initial formulas used   : 3
% 0.13/0.39  # Proof object generating inferences   : 8
% 0.13/0.39  # Proof object simplifying inferences  : 10
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 3
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 15
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 15
% 0.13/0.39  # Processed clauses                    : 54
% 0.13/0.39  # ...of these trivial                  : 3
% 0.13/0.39  # ...subsumed                          : 2
% 0.13/0.39  # ...remaining for further processing  : 49
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 1
% 0.13/0.39  # Backward-rewritten                   : 9
% 0.13/0.39  # Generated clauses                    : 35
% 0.13/0.39  # ...of the previous two non-trivial   : 32
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 30
% 0.13/0.39  # Factorizations                       : 2
% 0.13/0.39  # Equation resolutions                 : 3
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
% 0.13/0.39  # Current number of processed clauses  : 24
% 0.13/0.39  #    Positive orientable unit clauses  : 2
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 22
% 0.13/0.39  # Current number of unprocessed clauses: 6
% 0.13/0.39  # ...number of literals in the above   : 33
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 25
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 287
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 72
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 1
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 2291
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
