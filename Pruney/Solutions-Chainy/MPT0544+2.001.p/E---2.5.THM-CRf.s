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
% DateTime   : Thu Dec  3 10:50:28 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   26 (  71 expanded)
%              Number of clauses        :   17 (  33 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 324 expanded)
%              Number of equality atoms :   30 (  95 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t146_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(esk1_4(X6,X7,X8,X9),X9),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X12,X11),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(X16,esk2_3(X6,X13,X14)),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk3_3(X6,X13,X14),esk2_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(X20,esk4_3(X18,X19,X20)),X18)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X22,X23),X18)
        | r2_hidden(X22,X19)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(esk5_2(X24,X25),X27),X24)
        | X25 = k1_relat_1(X24) )
      & ( r2_hidden(esk5_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk5_2(X24,X25),esk6_2(X24,X25)),X24)
        | X25 = k1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,plain,(
    ! [X29,X30,X31,X33,X34,X35,X36,X38] :
      ( ( ~ r2_hidden(X31,X30)
        | r2_hidden(k4_tarski(esk7_3(X29,X30,X31),X31),X29)
        | X30 != k2_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X34,X33),X29)
        | r2_hidden(X33,X30)
        | X30 != k2_relat_1(X29) )
      & ( ~ r2_hidden(esk8_2(X35,X36),X36)
        | ~ r2_hidden(k4_tarski(X38,esk8_2(X35,X36)),X35)
        | X36 = k2_relat_1(X35) )
      & ( r2_hidden(esk8_2(X35,X36),X36)
        | r2_hidden(k4_tarski(esk9_2(X35,X36),esk8_2(X35,X36)),X35)
        | X36 = k2_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t146_relat_1])).

cnf(c_0_13,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk8_2(X2,X1),k9_relat_1(X2,X3))
    | r2_hidden(esk8_2(X2,X1),X1)
    | ~ r2_hidden(esk9_2(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk9_2(X2,X1),k1_relat_1(X2))
    | r2_hidden(esk8_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & k9_relat_1(esk10_0,k1_relat_1(esk10_0)) != k2_relat_1(esk10_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk8_2(X2,X1),k9_relat_1(X2,k1_relat_1(X2)))
    | r2_hidden(esk8_2(X2,X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( X1 = k2_relat_1(esk10_0)
    | r2_hidden(esk8_2(esk10_0,X1),k9_relat_1(esk10_0,k1_relat_1(esk10_0)))
    | r2_hidden(esk8_2(esk10_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( k9_relat_1(esk10_0,k1_relat_1(esk10_0)) != k2_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk8_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk8_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk8_2(esk10_0,k9_relat_1(esk10_0,k1_relat_1(esk10_0))),k9_relat_1(esk10_0,k1_relat_1(esk10_0))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),X3),X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk8_2(esk10_0,k9_relat_1(esk10_0,k1_relat_1(esk10_0)))),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_17])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.12/0.38  # and selection function SelectCQIArNXTEqFirst.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.12/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.12/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.38  fof(t146_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.12/0.38  fof(c_0_4, plain, ![X6, X7, X8, X9, X11, X12, X13, X14, X16]:((((r2_hidden(k4_tarski(esk1_4(X6,X7,X8,X9),X9),X6)|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|~v1_relat_1(X6))&(r2_hidden(esk1_4(X6,X7,X8,X9),X7)|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|~v1_relat_1(X6)))&(~r2_hidden(k4_tarski(X12,X11),X6)|~r2_hidden(X12,X7)|r2_hidden(X11,X8)|X8!=k9_relat_1(X6,X7)|~v1_relat_1(X6)))&((~r2_hidden(esk2_3(X6,X13,X14),X14)|(~r2_hidden(k4_tarski(X16,esk2_3(X6,X13,X14)),X6)|~r2_hidden(X16,X13))|X14=k9_relat_1(X6,X13)|~v1_relat_1(X6))&((r2_hidden(k4_tarski(esk3_3(X6,X13,X14),esk2_3(X6,X13,X14)),X6)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|~v1_relat_1(X6))&(r2_hidden(esk3_3(X6,X13,X14),X13)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.12/0.38  fof(c_0_5, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(X20,esk4_3(X18,X19,X20)),X18)|X19!=k1_relat_1(X18))&(~r2_hidden(k4_tarski(X22,X23),X18)|r2_hidden(X22,X19)|X19!=k1_relat_1(X18)))&((~r2_hidden(esk5_2(X24,X25),X25)|~r2_hidden(k4_tarski(esk5_2(X24,X25),X27),X24)|X25=k1_relat_1(X24))&(r2_hidden(esk5_2(X24,X25),X25)|r2_hidden(k4_tarski(esk5_2(X24,X25),esk6_2(X24,X25)),X24)|X25=k1_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.12/0.38  cnf(c_0_6, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  fof(c_0_7, plain, ![X29, X30, X31, X33, X34, X35, X36, X38]:(((~r2_hidden(X31,X30)|r2_hidden(k4_tarski(esk7_3(X29,X30,X31),X31),X29)|X30!=k2_relat_1(X29))&(~r2_hidden(k4_tarski(X34,X33),X29)|r2_hidden(X33,X30)|X30!=k2_relat_1(X29)))&((~r2_hidden(esk8_2(X35,X36),X36)|~r2_hidden(k4_tarski(X38,esk8_2(X35,X36)),X35)|X36=k2_relat_1(X35))&(r2_hidden(esk8_2(X35,X36),X36)|r2_hidden(k4_tarski(esk9_2(X35,X36),esk8_2(X35,X36)),X35)|X36=k2_relat_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.38  cnf(c_0_8, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_9, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_10, plain, (r2_hidden(esk8_2(X1,X2),X2)|r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_11, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_8])).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1))), inference(assume_negation,[status(cth)],[t146_relat_1])).
% 0.12/0.38  cnf(c_0_13, plain, (X1=k2_relat_1(X2)|r2_hidden(esk8_2(X2,X1),k9_relat_1(X2,X3))|r2_hidden(esk8_2(X2,X1),X1)|~r2_hidden(esk9_2(X2,X1),X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.38  cnf(c_0_14, plain, (X1=k2_relat_1(X2)|r2_hidden(esk9_2(X2,X1),k1_relat_1(X2))|r2_hidden(esk8_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_11, c_0_10])).
% 0.12/0.38  fof(c_0_15, negated_conjecture, (v1_relat_1(esk10_0)&k9_relat_1(esk10_0,k1_relat_1(esk10_0))!=k2_relat_1(esk10_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.38  cnf(c_0_16, plain, (X1=k2_relat_1(X2)|r2_hidden(esk8_2(X2,X1),k9_relat_1(X2,k1_relat_1(X2)))|r2_hidden(esk8_2(X2,X1),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (X1=k2_relat_1(esk10_0)|r2_hidden(esk8_2(esk10_0,X1),k9_relat_1(esk10_0,k1_relat_1(esk10_0)))|r2_hidden(esk8_2(esk10_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (k9_relat_1(esk10_0,k1_relat_1(esk10_0))!=k2_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),X4),X1)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_21, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk8_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk8_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk8_2(esk10_0,k9_relat_1(esk10_0,k1_relat_1(esk10_0))),k9_relat_1(esk10_0,k1_relat_1(esk10_0)))), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_18]), c_0_19])).
% 0.12/0.38  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),X3),X1)|~r2_hidden(X3,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk8_2(esk10_0,k9_relat_1(esk10_0,k1_relat_1(esk10_0)))),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_17])]), c_0_24]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 26
% 0.12/0.38  # Proof object clause steps            : 17
% 0.12/0.38  # Proof object formula steps           : 9
% 0.12/0.38  # Proof object conjectures             : 9
% 0.12/0.38  # Proof object clause conjectures      : 6
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 7
% 0.12/0.38  # Proof object initial formulas used   : 4
% 0.12/0.38  # Proof object generating inferences   : 7
% 0.12/0.38  # Proof object simplifying inferences  : 8
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 4
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 16
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 16
% 0.12/0.38  # Processed clauses                    : 65
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 3
% 0.12/0.38  # ...remaining for further processing  : 60
% 0.12/0.38  # Other redundant clauses eliminated   : 7
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 0
% 0.12/0.38  # Generated clauses                    : 106
% 0.12/0.38  # ...of the previous two non-trivial   : 101
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 93
% 0.12/0.38  # Factorizations                       : 6
% 0.12/0.38  # Equation resolutions                 : 7
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 37
% 0.12/0.38  #    Positive orientable unit clauses  : 3
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 32
% 0.12/0.38  # Current number of unprocessed clauses: 68
% 0.12/0.38  # ...number of literals in the above   : 235
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 16
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 159
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 71
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.38  # Unit Clause-clause subsumption calls : 6
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 0
% 0.12/0.38  # BW rewrite match successes           : 0
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 3800
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.033 s
% 0.12/0.38  # System time              : 0.002 s
% 0.12/0.38  # Total time               : 0.035 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
