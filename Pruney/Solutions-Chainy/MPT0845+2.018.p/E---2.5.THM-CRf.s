%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:56 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 (  55 expanded)
%              Number of clauses        :   17 (  25 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 190 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t1_mcart_1,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X34,X35,X37] :
      ( ( r2_hidden(esk7_2(X34,X35),X35)
        | ~ r2_hidden(X34,X35) )
      & ( ~ r2_hidden(X37,X35)
        | ~ r2_hidden(X37,esk7_2(X34,X35))
        | ~ r2_hidden(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t1_mcart_1])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk7_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_xboole_0(k2_tarski(X31,X32),X33)
      | ~ r2_hidden(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X13] : r1_xboole_0(X13,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ! [X39] :
      ( esk8_0 != k1_xboole_0
      & ( ~ r2_hidden(X39,esk8_0)
        | ~ r1_xboole_0(X39,esk8_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_14,plain,
    ( r1_xboole_0(esk7_2(X1,X2),X3)
    | ~ r2_hidden(esk1_2(esk7_2(X1,X2),X3),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X14,X15,X16,X17,X20,X21,X22,X23,X24,X25,X27,X28] :
      ( ( r2_hidden(esk2_4(X14,X15,X16,X17),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( r2_hidden(esk3_4(X14,X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( X17 = k4_tarski(esk2_4(X14,X15,X16,X17),esk3_4(X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( ~ r2_hidden(X21,X14)
        | ~ r2_hidden(X22,X15)
        | X20 != k4_tarski(X21,X22)
        | r2_hidden(X20,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( ~ r2_hidden(esk4_3(X23,X24,X25),X25)
        | ~ r2_hidden(X27,X23)
        | ~ r2_hidden(X28,X24)
        | esk4_3(X23,X24,X25) != k4_tarski(X27,X28)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( r2_hidden(esk5_3(X23,X24,X25),X23)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( r2_hidden(esk6_3(X23,X24,X25),X24)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( esk4_3(X23,X24,X25) = k4_tarski(esk5_3(X23,X24,X25),esk6_3(X23,X24,X25))
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r1_xboole_0(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_xboole_0(esk7_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( X1 = k2_zfmisc_1(k1_xboole_0,X2)
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,X1) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_27,plain,
    ( X1 = esk8_0
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 0.14/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.14/0.38  fof(t1_mcart_1, conjecture, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.14/0.38  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.14/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.38  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.14/0.38  fof(c_0_6, plain, ![X34, X35, X37]:((r2_hidden(esk7_2(X34,X35),X35)|~r2_hidden(X34,X35))&(~r2_hidden(X37,X35)|~r2_hidden(X37,esk7_2(X34,X35))|~r2_hidden(X34,X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1)))))), inference(assume_negation,[status(cth)],[t1_mcart_1])).
% 0.14/0.38  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk7_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_11, plain, ![X31, X32, X33]:(~r1_xboole_0(k2_tarski(X31,X32),X33)|~r2_hidden(X31,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.14/0.38  fof(c_0_12, plain, ![X13]:r1_xboole_0(X13,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.38  fof(c_0_13, negated_conjecture, ![X39]:(esk8_0!=k1_xboole_0&(~r2_hidden(X39,esk8_0)|~r1_xboole_0(X39,esk8_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.14/0.38  cnf(c_0_14, plain, (r1_xboole_0(esk7_2(X1,X2),X3)|~r2_hidden(esk1_2(esk7_2(X1,X2),X3),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_16, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_18, plain, ![X14, X15, X16, X17, X20, X21, X22, X23, X24, X25, X27, X28]:(((((r2_hidden(esk2_4(X14,X15,X16,X17),X14)|~r2_hidden(X17,X16)|X16!=k2_zfmisc_1(X14,X15))&(r2_hidden(esk3_4(X14,X15,X16,X17),X15)|~r2_hidden(X17,X16)|X16!=k2_zfmisc_1(X14,X15)))&(X17=k4_tarski(esk2_4(X14,X15,X16,X17),esk3_4(X14,X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k2_zfmisc_1(X14,X15)))&(~r2_hidden(X21,X14)|~r2_hidden(X22,X15)|X20!=k4_tarski(X21,X22)|r2_hidden(X20,X16)|X16!=k2_zfmisc_1(X14,X15)))&((~r2_hidden(esk4_3(X23,X24,X25),X25)|(~r2_hidden(X27,X23)|~r2_hidden(X28,X24)|esk4_3(X23,X24,X25)!=k4_tarski(X27,X28))|X25=k2_zfmisc_1(X23,X24))&(((r2_hidden(esk5_3(X23,X24,X25),X23)|r2_hidden(esk4_3(X23,X24,X25),X25)|X25=k2_zfmisc_1(X23,X24))&(r2_hidden(esk6_3(X23,X24,X25),X24)|r2_hidden(esk4_3(X23,X24,X25),X25)|X25=k2_zfmisc_1(X23,X24)))&(esk4_3(X23,X24,X25)=k4_tarski(esk5_3(X23,X24,X25),esk6_3(X23,X24,X25))|r2_hidden(esk4_3(X23,X24,X25),X25)|X25=k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (~r2_hidden(X1,esk8_0)|~r1_xboole_0(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_20, plain, (r1_xboole_0(esk7_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(esk7_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_23, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.14/0.38  cnf(c_0_25, plain, (X1=k2_zfmisc_1(k1_xboole_0,X2)|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,X1)=esk8_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_27, plain, (X1=esk8_0|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_29, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_27]), c_0_28]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 30
% 0.14/0.38  # Proof object clause steps            : 17
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 7
% 0.14/0.38  # Proof object clause conjectures      : 4
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 9
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 7
% 0.14/0.38  # Proof object simplifying inferences  : 3
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 17
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 237
% 0.14/0.38  # ...of these trivial                  : 18
% 0.14/0.38  # ...subsumed                          : 101
% 0.14/0.38  # ...remaining for further processing  : 118
% 0.14/0.38  # Other redundant clauses eliminated   : 5
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 19
% 0.14/0.38  # Generated clauses                    : 612
% 0.14/0.38  # ...of the previous two non-trivial   : 553
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 608
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 5
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 78
% 0.14/0.38  #    Positive orientable unit clauses  : 15
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 20
% 0.14/0.38  #    Non-unit-clauses                  : 43
% 0.14/0.38  # Current number of unprocessed clauses: 329
% 0.14/0.38  # ...number of literals in the above   : 573
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 36
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 370
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 257
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 18
% 0.14/0.38  # Unit Clause-clause subsumption calls : 148
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 9
% 0.14/0.38  # BW rewrite match successes           : 5
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 6432
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.037 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.041 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
