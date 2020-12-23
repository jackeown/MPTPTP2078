%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   30 (  81 expanded)
%              Number of clauses        :   19 (  37 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 289 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_5,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] : r1_setfam_1(X1,k2_setfam_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t29_setfam_1])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X19,X20,X22] :
      ( ( r2_hidden(esk2_3(X15,X16,X17),X16)
        | ~ r2_hidden(X17,X15)
        | ~ r1_setfam_1(X15,X16) )
      & ( r1_tarski(X17,esk2_3(X15,X16,X17))
        | ~ r2_hidden(X17,X15)
        | ~ r1_setfam_1(X15,X16) )
      & ( r2_hidden(esk3_2(X19,X20),X19)
        | r1_setfam_1(X19,X20) )
      & ( ~ r2_hidden(X22,X20)
        | ~ r1_tarski(esk3_2(X19,X20),X22)
        | r1_setfam_1(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_9,plain,(
    ! [X23,X24,X25,X26,X29,X30,X31,X32,X33,X34,X36,X37] :
      ( ( r2_hidden(esk4_4(X23,X24,X25,X26),X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k2_setfam_1(X23,X24) )
      & ( r2_hidden(esk5_4(X23,X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k2_setfam_1(X23,X24) )
      & ( X26 = k2_xboole_0(esk4_4(X23,X24,X25,X26),esk5_4(X23,X24,X25,X26))
        | ~ r2_hidden(X26,X25)
        | X25 != k2_setfam_1(X23,X24) )
      & ( ~ r2_hidden(X30,X23)
        | ~ r2_hidden(X31,X24)
        | X29 != k2_xboole_0(X30,X31)
        | r2_hidden(X29,X25)
        | X25 != k2_setfam_1(X23,X24) )
      & ( ~ r2_hidden(esk6_3(X32,X33,X34),X34)
        | ~ r2_hidden(X36,X32)
        | ~ r2_hidden(X37,X33)
        | esk6_3(X32,X33,X34) != k2_xboole_0(X36,X37)
        | X34 = k2_setfam_1(X32,X33) )
      & ( r2_hidden(esk7_3(X32,X33,X34),X32)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k2_setfam_1(X32,X33) )
      & ( r2_hidden(esk8_3(X32,X33,X34),X33)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k2_setfam_1(X32,X33) )
      & ( esk6_3(X32,X33,X34) = k2_xboole_0(esk7_3(X32,X33,X34),esk8_3(X32,X33,X34))
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k2_setfam_1(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_setfam_1])])])])])])).

cnf(c_0_10,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,negated_conjecture,(
    ~ r1_setfam_1(esk9_0,k2_setfam_1(esk9_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk3_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k2_xboole_0(X1,X3)
    | X6 != k2_setfam_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_setfam_1(esk9_0,k2_setfam_1(esk9_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_setfam_1(X1,X2)
    | r2_hidden(esk1_2(esk3_2(X1,X2),X3),esk3_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),k2_setfam_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),X1),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)))
    | ~ r2_hidden(X1,k2_setfam_1(esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_setfam_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),X1),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0))),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),k2_setfam_1(esk9_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_27]),c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.13/0.37  # and selection function SelectCQIArNXTEqFirst.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(t29_setfam_1, conjecture, ![X1]:r1_setfam_1(X1,k2_setfam_1(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 0.13/0.37  fof(d2_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,X2)&r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 0.13/0.37  fof(d4_setfam_1, axiom, ![X1, X2, X3]:(X3=k2_setfam_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k2_xboole_0(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 0.13/0.37  fof(c_0_5, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.37  fof(c_0_6, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:r1_setfam_1(X1,k2_setfam_1(X1,X1))), inference(assume_negation,[status(cth)],[t29_setfam_1])).
% 0.13/0.37  fof(c_0_8, plain, ![X15, X16, X17, X19, X20, X22]:(((r2_hidden(esk2_3(X15,X16,X17),X16)|~r2_hidden(X17,X15)|~r1_setfam_1(X15,X16))&(r1_tarski(X17,esk2_3(X15,X16,X17))|~r2_hidden(X17,X15)|~r1_setfam_1(X15,X16)))&((r2_hidden(esk3_2(X19,X20),X19)|r1_setfam_1(X19,X20))&(~r2_hidden(X22,X20)|~r1_tarski(esk3_2(X19,X20),X22)|r1_setfam_1(X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X23, X24, X25, X26, X29, X30, X31, X32, X33, X34, X36, X37]:(((((r2_hidden(esk4_4(X23,X24,X25,X26),X23)|~r2_hidden(X26,X25)|X25!=k2_setfam_1(X23,X24))&(r2_hidden(esk5_4(X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|X25!=k2_setfam_1(X23,X24)))&(X26=k2_xboole_0(esk4_4(X23,X24,X25,X26),esk5_4(X23,X24,X25,X26))|~r2_hidden(X26,X25)|X25!=k2_setfam_1(X23,X24)))&(~r2_hidden(X30,X23)|~r2_hidden(X31,X24)|X29!=k2_xboole_0(X30,X31)|r2_hidden(X29,X25)|X25!=k2_setfam_1(X23,X24)))&((~r2_hidden(esk6_3(X32,X33,X34),X34)|(~r2_hidden(X36,X32)|~r2_hidden(X37,X33)|esk6_3(X32,X33,X34)!=k2_xboole_0(X36,X37))|X34=k2_setfam_1(X32,X33))&(((r2_hidden(esk7_3(X32,X33,X34),X32)|r2_hidden(esk6_3(X32,X33,X34),X34)|X34=k2_setfam_1(X32,X33))&(r2_hidden(esk8_3(X32,X33,X34),X33)|r2_hidden(esk6_3(X32,X33,X34),X34)|X34=k2_setfam_1(X32,X33)))&(esk6_3(X32,X33,X34)=k2_xboole_0(esk7_3(X32,X33,X34),esk8_3(X32,X33,X34))|r2_hidden(esk6_3(X32,X33,X34),X34)|X34=k2_setfam_1(X32,X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_setfam_1])])])])])])).
% 0.13/0.37  cnf(c_0_10, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~r1_setfam_1(esk9_0,k2_setfam_1(esk9_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.37  cnf(c_0_13, plain, (r1_setfam_1(X3,X2)|~r2_hidden(X1,X2)|~r1_tarski(esk3_2(X3,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k2_xboole_0(X1,X3)|X6!=k2_setfam_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (~r1_setfam_1(esk9_0,k2_setfam_1(esk9_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_18, plain, (r1_setfam_1(X1,X2)|r2_hidden(esk1_2(esk3_2(X1,X2),X3),esk3_2(X1,X2))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.13/0.37  cnf(c_0_19, plain, (r2_hidden(k2_xboole_0(X1,X2),k2_setfam_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_xboole_0(X1,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_10])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_2(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),X1),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)))|~r2_hidden(X1,k2_setfam_1(esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_22, plain, (r2_hidden(X1,k2_setfam_1(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_23, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),X1),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0))),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)))), inference(spm,[status(thm)],[c_0_15, c_0_26])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (~r2_hidden(esk3_2(esk9_0,k2_setfam_1(esk9_0,esk9_0)),k2_setfam_1(esk9_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_27]), c_0_17])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_25])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 30
% 0.13/0.37  # Proof object clause steps            : 19
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 7
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 6
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 17
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 17
% 0.13/0.37  # Processed clauses                    : 47
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 47
% 0.13/0.37  # Other redundant clauses eliminated   : 6
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 53
% 0.13/0.37  # ...of the previous two non-trivial   : 49
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 48
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 6
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
% 0.13/0.37  # Current number of processed clauses  : 26
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 20
% 0.13/0.37  # Current number of unprocessed clauses: 36
% 0.13/0.37  # ...number of literals in the above   : 106
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 17
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 31
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 23
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 3
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2137
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.032 s
% 0.13/0.37  # System time              : 0.001 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
