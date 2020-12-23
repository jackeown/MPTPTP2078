%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 (  37 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 209 expanded)
%              Number of equality atoms :   35 (  69 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t103_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

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

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X4,X1)
          & ! [X5,X6] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & X4 = k4_tarski(X5,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t103_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X18,X19,X20,X21,X24,X25,X26,X27,X28,X29,X31,X32] :
      ( ( r2_hidden(esk2_4(X18,X19,X20,X21),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk3_4(X18,X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( X21 = k4_tarski(esk2_4(X18,X19,X20,X21),esk3_4(X18,X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( ~ r2_hidden(X25,X18)
        | ~ r2_hidden(X26,X19)
        | X24 != k4_tarski(X25,X26)
        | r2_hidden(X24,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( ~ r2_hidden(esk4_3(X27,X28,X29),X29)
        | ~ r2_hidden(X31,X27)
        | ~ r2_hidden(X32,X28)
        | esk4_3(X27,X28,X29) != k4_tarski(X31,X32)
        | X29 = k2_zfmisc_1(X27,X28) )
      & ( r2_hidden(esk5_3(X27,X28,X29),X27)
        | r2_hidden(esk4_3(X27,X28,X29),X29)
        | X29 = k2_zfmisc_1(X27,X28) )
      & ( r2_hidden(esk6_3(X27,X28,X29),X28)
        | r2_hidden(esk4_3(X27,X28,X29),X29)
        | X29 = k2_zfmisc_1(X27,X28) )
      & ( esk4_3(X27,X28,X29) = k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29))
        | r2_hidden(esk4_3(X27,X28,X29),X29)
        | X29 = k2_zfmisc_1(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X39,X40] :
      ( r1_tarski(esk7_0,k2_zfmisc_1(esk8_0,esk9_0))
      & r2_hidden(esk10_0,esk7_0)
      & ( ~ r2_hidden(X39,esk8_0)
        | ~ r2_hidden(X40,esk9_0)
        | esk10_0 != k4_tarski(X39,X40) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( X1 = k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk9_0)
    | esk10_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk10_0),esk9_0)
    | ~ r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk10_0),esk8_0)
    | ~ r2_hidden(esk10_0,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk2_4(X1,esk9_0,k2_zfmisc_1(X1,esk9_0),esk10_0),esk8_0)
    | ~ r2_hidden(esk10_0,k2_zfmisc_1(X1,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(esk7_0,k2_zfmisc_1(esk8_0,esk9_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk10_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:35:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.018 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t103_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 0.12/0.36  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.12/0.36  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.12/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.36  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6)))))), inference(assume_negation,[status(cth)],[t103_zfmisc_1])).
% 0.12/0.36  fof(c_0_5, plain, ![X18, X19, X20, X21, X24, X25, X26, X27, X28, X29, X31, X32]:(((((r2_hidden(esk2_4(X18,X19,X20,X21),X18)|~r2_hidden(X21,X20)|X20!=k2_zfmisc_1(X18,X19))&(r2_hidden(esk3_4(X18,X19,X20,X21),X19)|~r2_hidden(X21,X20)|X20!=k2_zfmisc_1(X18,X19)))&(X21=k4_tarski(esk2_4(X18,X19,X20,X21),esk3_4(X18,X19,X20,X21))|~r2_hidden(X21,X20)|X20!=k2_zfmisc_1(X18,X19)))&(~r2_hidden(X25,X18)|~r2_hidden(X26,X19)|X24!=k4_tarski(X25,X26)|r2_hidden(X24,X20)|X20!=k2_zfmisc_1(X18,X19)))&((~r2_hidden(esk4_3(X27,X28,X29),X29)|(~r2_hidden(X31,X27)|~r2_hidden(X32,X28)|esk4_3(X27,X28,X29)!=k4_tarski(X31,X32))|X29=k2_zfmisc_1(X27,X28))&(((r2_hidden(esk5_3(X27,X28,X29),X27)|r2_hidden(esk4_3(X27,X28,X29),X29)|X29=k2_zfmisc_1(X27,X28))&(r2_hidden(esk6_3(X27,X28,X29),X28)|r2_hidden(esk4_3(X27,X28,X29),X29)|X29=k2_zfmisc_1(X27,X28)))&(esk4_3(X27,X28,X29)=k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29))|r2_hidden(esk4_3(X27,X28,X29),X29)|X29=k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.12/0.36  fof(c_0_6, negated_conjecture, ![X39, X40]:((r1_tarski(esk7_0,k2_zfmisc_1(esk8_0,esk9_0))&r2_hidden(esk10_0,esk7_0))&(~r2_hidden(X39,esk8_0)|~r2_hidden(X40,esk9_0)|esk10_0!=k4_tarski(X39,X40))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.12/0.36  cnf(c_0_7, plain, (X1=k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_8, negated_conjecture, (~r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk9_0)|esk10_0!=k4_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_9, plain, (k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_10, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  fof(c_0_11, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.12/0.36  fof(c_0_12, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (~r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk10_0),esk9_0)|~r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk10_0),esk8_0)|~r2_hidden(esk10_0,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9])])).
% 0.12/0.36  cnf(c_0_14, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_15, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_16, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_18, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (~r2_hidden(esk2_4(X1,esk9_0,k2_zfmisc_1(X1,esk9_0),esk10_0),esk8_0)|~r2_hidden(esk10_0,k2_zfmisc_1(X1,esk9_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.36  cnf(c_0_20, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_21, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (k2_xboole_0(esk7_0,k2_zfmisc_1(esk8_0,esk9_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (r2_hidden(esk10_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 27
% 0.12/0.36  # Proof object clause steps            : 18
% 0.12/0.36  # Proof object formula steps           : 9
% 0.12/0.36  # Proof object conjectures             : 12
% 0.12/0.36  # Proof object clause conjectures      : 9
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 8
% 0.12/0.36  # Proof object initial formulas used   : 4
% 0.12/0.36  # Proof object generating inferences   : 6
% 0.12/0.36  # Proof object simplifying inferences  : 7
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 4
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 18
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 18
% 0.12/0.36  # Processed clauses                    : 49
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 49
% 0.12/0.36  # Other redundant clauses eliminated   : 9
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 0
% 0.12/0.36  # Generated clauses                    : 38
% 0.12/0.36  # ...of the previous two non-trivial   : 32
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 30
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 9
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 24
% 0.12/0.36  #    Positive orientable unit clauses  : 3
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 20
% 0.12/0.36  # Current number of unprocessed clauses: 19
% 0.12/0.36  # ...number of literals in the above   : 77
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 18
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 117
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 84
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 7
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 0
% 0.12/0.36  # BW rewrite match successes           : 0
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 2065
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.018 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.023 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
