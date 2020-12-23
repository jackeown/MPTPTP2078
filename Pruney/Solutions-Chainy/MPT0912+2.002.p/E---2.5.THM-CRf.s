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
% DateTime   : Thu Dec  3 11:00:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  46 expanded)
%              Number of clauses        :   18 (  24 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 292 expanded)
%              Number of equality atoms :   34 ( 112 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
        & ! [X5,X6,X7] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & r2_hidden(X7,X4)
              & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
          & ! [X5,X6,X7] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & r2_hidden(X7,X4)
                & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    inference(assume_negation,[status(cth)],[t72_mcart_1])).

fof(c_0_5,negated_conjecture,(
    ! [X35,X36,X37] :
      ( r2_hidden(esk6_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
      & ( ~ r2_hidden(X35,esk7_0)
        | ~ r2_hidden(X36,esk8_0)
        | ~ r2_hidden(X37,esk9_0)
        | esk6_0 != k3_mcart_1(X35,X36,X37) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X25,X26,X27] : k3_mcart_1(X25,X26,X27) = k4_tarski(k4_tarski(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X14,X15,X16,X17,X18,X19,X21,X22] :
      ( ( r2_hidden(esk1_4(X8,X9,X10,X11),X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( r2_hidden(esk2_4(X8,X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( X11 = k4_tarski(esk1_4(X8,X9,X10,X11),esk2_4(X8,X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( ~ r2_hidden(X15,X8)
        | ~ r2_hidden(X16,X9)
        | X14 != k4_tarski(X15,X16)
        | r2_hidden(X14,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( ~ r2_hidden(esk3_3(X17,X18,X19),X19)
        | ~ r2_hidden(X21,X17)
        | ~ r2_hidden(X22,X18)
        | esk3_3(X17,X18,X19) != k4_tarski(X21,X22)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X17)
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk5_3(X17,X18,X19),X18)
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( esk3_3(X17,X18,X19) = k4_tarski(esk4_3(X17,X18,X19),esk5_3(X17,X18,X19))
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X3,esk9_0)
    | esk6_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( esk6_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(esk2_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk8_0)
    | ~ r2_hidden(esk1_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(esk1_4(X3,esk8_0,k2_zfmisc_1(X3,esk8_0),X1),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_20,plain,(
    ! [X28,X29,X30] : k3_zfmisc_1(X28,X29,X30) = k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk7_0,esk8_0),X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1),X2),X3) != esk6_0
    | ~ r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1))
    | ~ r2_hidden(X3,esk9_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk2_4(k2_zfmisc_1(esk7_0,esk8_0),X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1),esk6_0),esk9_0)
    | ~ r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_15]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t72_mcart_1, conjecture, ![X1, X2, X3, X4]:~((r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))&![X5, X6, X7]:~((((r2_hidden(X5,X2)&r2_hidden(X6,X3))&r2_hidden(X7,X4))&X1=k3_mcart_1(X5,X6,X7))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 0.19/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.37  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:~((r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))&![X5, X6, X7]:~((((r2_hidden(X5,X2)&r2_hidden(X6,X3))&r2_hidden(X7,X4))&X1=k3_mcart_1(X5,X6,X7)))))), inference(assume_negation,[status(cth)],[t72_mcart_1])).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ![X35, X36, X37]:(r2_hidden(esk6_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&(~r2_hidden(X35,esk7_0)|~r2_hidden(X36,esk8_0)|~r2_hidden(X37,esk9_0)|esk6_0!=k3_mcart_1(X35,X36,X37))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.19/0.37  fof(c_0_6, plain, ![X25, X26, X27]:k3_mcart_1(X25,X26,X27)=k4_tarski(k4_tarski(X25,X26),X27), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.37  fof(c_0_7, plain, ![X8, X9, X10, X11, X14, X15, X16, X17, X18, X19, X21, X22]:(((((r2_hidden(esk1_4(X8,X9,X10,X11),X8)|~r2_hidden(X11,X10)|X10!=k2_zfmisc_1(X8,X9))&(r2_hidden(esk2_4(X8,X9,X10,X11),X9)|~r2_hidden(X11,X10)|X10!=k2_zfmisc_1(X8,X9)))&(X11=k4_tarski(esk1_4(X8,X9,X10,X11),esk2_4(X8,X9,X10,X11))|~r2_hidden(X11,X10)|X10!=k2_zfmisc_1(X8,X9)))&(~r2_hidden(X15,X8)|~r2_hidden(X16,X9)|X14!=k4_tarski(X15,X16)|r2_hidden(X14,X10)|X10!=k2_zfmisc_1(X8,X9)))&((~r2_hidden(esk3_3(X17,X18,X19),X19)|(~r2_hidden(X21,X17)|~r2_hidden(X22,X18)|esk3_3(X17,X18,X19)!=k4_tarski(X21,X22))|X19=k2_zfmisc_1(X17,X18))&(((r2_hidden(esk4_3(X17,X18,X19),X17)|r2_hidden(esk3_3(X17,X18,X19),X19)|X19=k2_zfmisc_1(X17,X18))&(r2_hidden(esk5_3(X17,X18,X19),X18)|r2_hidden(esk3_3(X17,X18,X19),X19)|X19=k2_zfmisc_1(X17,X18)))&(esk3_3(X17,X18,X19)=k4_tarski(esk4_3(X17,X18,X19),esk5_3(X17,X18,X19))|r2_hidden(esk3_3(X17,X18,X19),X19)|X19=k2_zfmisc_1(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.37  cnf(c_0_8, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X3,esk9_0)|esk6_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_9, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_10, plain, (X1=k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (esk6_0!=k4_tarski(k4_tarski(X1,X2),X3)|~r2_hidden(X3,esk9_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.37  cnf(c_0_12, plain, (k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_13, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (k4_tarski(X1,X2)!=esk6_0|~r2_hidden(esk2_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk8_0)|~r2_hidden(esk1_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk7_0)|~r2_hidden(X1,k2_zfmisc_1(X3,X4))|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_15, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_16, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (k4_tarski(X1,X2)!=esk6_0|~r2_hidden(esk1_4(X3,esk8_0,k2_zfmisc_1(X3,esk8_0),X1),esk7_0)|~r2_hidden(X1,k2_zfmisc_1(X3,esk8_0))|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.37  cnf(c_0_18, plain, (r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (k4_tarski(X1,X2)!=esk6_0|~r2_hidden(X1,k2_zfmisc_1(esk7_0,esk8_0))|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  fof(c_0_20, plain, ![X28, X29, X30]:k3_zfmisc_1(X28,X29,X30)=k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk7_0,esk8_0),X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1),X2),X3)!=esk6_0|~r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1))|~r2_hidden(X3,esk9_0)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk6_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_23, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (~r2_hidden(esk2_4(k2_zfmisc_1(esk7_0,esk8_0),X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1),esk6_0),esk9_0)|~r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_12])])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_15]), c_0_25])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 27
% 0.19/0.37  # Proof object clause steps            : 18
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 13
% 0.19/0.37  # Proof object clause conjectures      : 10
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 7
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 6
% 0.19/0.37  # Proof object simplifying inferences  : 8
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 12
% 0.19/0.37  # Removed in clause preprocessing      : 2
% 0.19/0.37  # Initial clauses in saturation        : 10
% 0.19/0.37  # Processed clauses                    : 32
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 31
% 0.19/0.37  # Other redundant clauses eliminated   : 6
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 22
% 0.19/0.37  # ...of the previous two non-trivial   : 20
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 17
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 6
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 17
% 0.19/0.37  #    Positive orientable unit clauses  : 1
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 0
% 0.19/0.37  #    Non-unit-clauses                  : 16
% 0.19/0.37  # Current number of unprocessed clauses: 8
% 0.19/0.37  # ...number of literals in the above   : 37
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 12
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 15
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1537
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.027 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
