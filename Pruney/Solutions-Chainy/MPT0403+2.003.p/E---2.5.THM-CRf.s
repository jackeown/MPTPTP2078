%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:34 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 (  65 expanded)
%              Number of clauses        :   19 (  30 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 261 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_setfam_1,conjecture,(
    ! [X1] : r1_setfam_1(X1,k2_setfam_1(X1,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_setfam_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k2_xboole_0(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : r1_setfam_1(X1,k2_setfam_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t29_setfam_1])).

fof(c_0_6,plain,(
    ! [X22,X23,X24,X26,X27,X29] :
      ( ( r2_hidden(esk3_3(X22,X23,X24),X23)
        | ~ r2_hidden(X24,X22)
        | ~ r1_setfam_1(X22,X23) )
      & ( r1_tarski(X24,esk3_3(X22,X23,X24))
        | ~ r2_hidden(X24,X22)
        | ~ r1_setfam_1(X22,X23) )
      & ( r2_hidden(esk4_2(X26,X27),X26)
        | r1_setfam_1(X26,X27) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r1_tarski(esk4_2(X26,X27),X29)
        | r1_setfam_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ r1_setfam_1(esk10_0,k2_setfam_1(esk10_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk4_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X30,X31,X32,X33,X36,X37,X38,X39,X40,X41,X43,X44] :
      ( ( r2_hidden(esk5_4(X30,X31,X32,X33),X30)
        | ~ r2_hidden(X33,X32)
        | X32 != k2_setfam_1(X30,X31) )
      & ( r2_hidden(esk6_4(X30,X31,X32,X33),X31)
        | ~ r2_hidden(X33,X32)
        | X32 != k2_setfam_1(X30,X31) )
      & ( X33 = k2_xboole_0(esk5_4(X30,X31,X32,X33),esk6_4(X30,X31,X32,X33))
        | ~ r2_hidden(X33,X32)
        | X32 != k2_setfam_1(X30,X31) )
      & ( ~ r2_hidden(X37,X30)
        | ~ r2_hidden(X38,X31)
        | X36 != k2_xboole_0(X37,X38)
        | r2_hidden(X36,X32)
        | X32 != k2_setfam_1(X30,X31) )
      & ( ~ r2_hidden(esk7_3(X39,X40,X41),X41)
        | ~ r2_hidden(X43,X39)
        | ~ r2_hidden(X44,X40)
        | esk7_3(X39,X40,X41) != k2_xboole_0(X43,X44)
        | X41 = k2_setfam_1(X39,X40) )
      & ( r2_hidden(esk8_3(X39,X40,X41),X39)
        | r2_hidden(esk7_3(X39,X40,X41),X41)
        | X41 = k2_setfam_1(X39,X40) )
      & ( r2_hidden(esk9_3(X39,X40,X41),X40)
        | r2_hidden(esk7_3(X39,X40,X41),X41)
        | X41 = k2_setfam_1(X39,X40) )
      & ( esk7_3(X39,X40,X41) = k2_xboole_0(esk8_3(X39,X40,X41),esk9_3(X39,X40,X41))
        | r2_hidden(esk7_3(X39,X40,X41),X41)
        | X41 = k2_setfam_1(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_setfam_1])])])])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_setfam_1(esk10_0,k2_setfam_1(esk10_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_setfam_1(X1,X2)
    | r2_hidden(esk1_2(esk4_2(X1,X2),X3),esk4_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k2_xboole_0(X1,X3)
    | X6 != k2_setfam_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),X1),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))
    | ~ r2_hidden(X1,k2_setfam_1(esk10_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),k2_setfam_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(X1,X2)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))
    | ~ r2_hidden(X2,esk10_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(X1,esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0))),k2_setfam_1(esk10_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_27]),c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.14/0.37  # and selection function SelectCQIArNXTEqFirst.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.016 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t29_setfam_1, conjecture, ![X1]:r1_setfam_1(X1,k2_setfam_1(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 0.14/0.37  fof(d2_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,X2)&r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 0.14/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.37  fof(d4_setfam_1, axiom, ![X1, X2, X3]:(X3=k2_setfam_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k2_xboole_0(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 0.14/0.37  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.14/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:r1_setfam_1(X1,k2_setfam_1(X1,X1))), inference(assume_negation,[status(cth)],[t29_setfam_1])).
% 0.14/0.37  fof(c_0_6, plain, ![X22, X23, X24, X26, X27, X29]:(((r2_hidden(esk3_3(X22,X23,X24),X23)|~r2_hidden(X24,X22)|~r1_setfam_1(X22,X23))&(r1_tarski(X24,esk3_3(X22,X23,X24))|~r2_hidden(X24,X22)|~r1_setfam_1(X22,X23)))&((r2_hidden(esk4_2(X26,X27),X26)|r1_setfam_1(X26,X27))&(~r2_hidden(X29,X27)|~r1_tarski(esk4_2(X26,X27),X29)|r1_setfam_1(X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).
% 0.14/0.37  fof(c_0_7, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.37  fof(c_0_8, negated_conjecture, ~r1_setfam_1(esk10_0,k2_setfam_1(esk10_0,esk10_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.37  cnf(c_0_9, plain, (r1_setfam_1(X3,X2)|~r2_hidden(X1,X2)|~r1_tarski(esk4_2(X3,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  fof(c_0_11, plain, ![X30, X31, X32, X33, X36, X37, X38, X39, X40, X41, X43, X44]:(((((r2_hidden(esk5_4(X30,X31,X32,X33),X30)|~r2_hidden(X33,X32)|X32!=k2_setfam_1(X30,X31))&(r2_hidden(esk6_4(X30,X31,X32,X33),X31)|~r2_hidden(X33,X32)|X32!=k2_setfam_1(X30,X31)))&(X33=k2_xboole_0(esk5_4(X30,X31,X32,X33),esk6_4(X30,X31,X32,X33))|~r2_hidden(X33,X32)|X32!=k2_setfam_1(X30,X31)))&(~r2_hidden(X37,X30)|~r2_hidden(X38,X31)|X36!=k2_xboole_0(X37,X38)|r2_hidden(X36,X32)|X32!=k2_setfam_1(X30,X31)))&((~r2_hidden(esk7_3(X39,X40,X41),X41)|(~r2_hidden(X43,X39)|~r2_hidden(X44,X40)|esk7_3(X39,X40,X41)!=k2_xboole_0(X43,X44))|X41=k2_setfam_1(X39,X40))&(((r2_hidden(esk8_3(X39,X40,X41),X39)|r2_hidden(esk7_3(X39,X40,X41),X41)|X41=k2_setfam_1(X39,X40))&(r2_hidden(esk9_3(X39,X40,X41),X40)|r2_hidden(esk7_3(X39,X40,X41),X41)|X41=k2_setfam_1(X39,X40)))&(esk7_3(X39,X40,X41)=k2_xboole_0(esk8_3(X39,X40,X41),esk9_3(X39,X40,X41))|r2_hidden(esk7_3(X39,X40,X41),X41)|X41=k2_setfam_1(X39,X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_setfam_1])])])])])])).
% 0.14/0.37  cnf(c_0_12, negated_conjecture, (~r1_setfam_1(esk10_0,k2_setfam_1(esk10_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_13, plain, (r1_setfam_1(X1,X2)|r2_hidden(esk1_2(esk4_2(X1,X2),X3),esk4_2(X1,X2))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.37  cnf(c_0_14, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k2_xboole_0(X1,X3)|X6!=k2_setfam_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  fof(c_0_15, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),X1),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))|~r2_hidden(X1,k2_setfam_1(esk10_0,esk10_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.37  cnf(c_0_17, plain, (r2_hidden(k2_xboole_0(X1,X2),k2_setfam_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).
% 0.14/0.37  cnf(c_0_18, plain, (r2_hidden(esk4_2(X1,X2),X1)|r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_19, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(X1,X2)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))|~r2_hidden(X2,esk10_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk10_0)), inference(spm,[status(thm)],[c_0_12, c_0_18])).
% 0.14/0.37  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_23, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_19])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(X1,esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.37  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)))), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),k2_xboole_0(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0))))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (~r2_hidden(k2_xboole_0(esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0)),esk4_2(esk10_0,k2_setfam_1(esk10_0,esk10_0))),k2_setfam_1(esk10_0,esk10_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_27]), c_0_12])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_21])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 30
% 0.14/0.37  # Proof object clause steps            : 19
% 0.14/0.37  # Proof object formula steps           : 11
% 0.14/0.37  # Proof object conjectures             : 12
% 0.14/0.37  # Proof object clause conjectures      : 9
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 7
% 0.14/0.37  # Proof object initial formulas used   : 5
% 0.14/0.37  # Proof object generating inferences   : 10
% 0.14/0.37  # Proof object simplifying inferences  : 6
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 5
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 22
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 22
% 0.14/0.37  # Processed clauses                    : 63
% 0.14/0.37  # ...of these trivial                  : 1
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 62
% 0.14/0.37  # Other redundant clauses eliminated   : 8
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 57
% 0.14/0.37  # ...of the previous two non-trivial   : 54
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 50
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 8
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
% 0.14/0.37  # Current number of processed clauses  : 33
% 0.14/0.37  #    Positive orientable unit clauses  : 3
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 28
% 0.14/0.37  # Current number of unprocessed clauses: 35
% 0.14/0.37  # ...number of literals in the above   : 110
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 22
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 128
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 99
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 0
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 2
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 2754
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.018 s
% 0.14/0.37  # System time              : 0.003 s
% 0.14/0.37  # Total time               : 0.021 s
% 0.14/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
