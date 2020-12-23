%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:54 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of clauses        :   18 (  26 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 145 expanded)
%              Number of equality atoms :   54 (  86 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t75_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

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

fof(t60_relat_1,conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ( r2_hidden(X8,X9)
        | ~ r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))) )
      & ( X8 != X10
        | ~ r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))) )
      & ( ~ r2_hidden(X8,X9)
        | X8 = X10
        | r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_9,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X11,X12,X13] :
      ( ( k4_xboole_0(X11,k2_tarski(X12,X13)) != k1_xboole_0
        | X11 = k1_xboole_0
        | X11 = k1_tarski(X12)
        | X11 = k1_tarski(X13)
        | X11 = k2_tarski(X12,X13) )
      & ( X11 != k1_xboole_0
        | k4_xboole_0(X11,k2_tarski(X12,X13)) = k1_xboole_0 )
      & ( X11 != k1_tarski(X12)
        | k4_xboole_0(X11,k2_tarski(X12,X13)) = k1_xboole_0 )
      & ( X11 != k1_tarski(X13)
        | k4_xboole_0(X11,k2_tarski(X12,X13)) = k1_xboole_0 )
      & ( X11 != k2_tarski(X12,X13)
        | k4_xboole_0(X11,k2_tarski(X12,X13)) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_zfmisc_1])])])).

cnf(c_0_12,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(k4_tarski(X16,esk2_3(X14,X15,X16)),X14)
        | X15 != k1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X18,X19),X14)
        | r2_hidden(X18,X15)
        | X15 != k1_relat_1(X14) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X21)
        | ~ r2_hidden(k4_tarski(esk3_2(X20,X21),X23),X20)
        | X21 = k1_relat_1(X20) )
      & ( r2_hidden(esk3_2(X20,X21),X21)
        | r2_hidden(k4_tarski(esk3_2(X20,X21),esk4_2(X20,X21)),X20)
        | X21 = k1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X25,X26,X27,X29,X30,X31,X32,X34] :
      ( ( ~ r2_hidden(X27,X26)
        | r2_hidden(k4_tarski(esk5_3(X25,X26,X27),X27),X25)
        | X26 != k2_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(X30,X29),X25)
        | r2_hidden(X29,X26)
        | X26 != k2_relat_1(X25) )
      & ( ~ r2_hidden(esk6_2(X31,X32),X32)
        | ~ r2_hidden(k4_tarski(X34,esk6_2(X31,X32)),X31)
        | X32 = k2_relat_1(X31) )
      & ( r2_hidden(esk6_2(X31,X32),X32)
        | r2_hidden(k4_tarski(esk7_2(X31,X32),esk6_2(X31,X32)),X31)
        | X32 = k2_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_relat_1])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_nnf,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_32,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n024.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 10:00:51 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.31  # Version: 2.5pre002
% 0.16/0.32  # No SInE strategy applied
% 0.16/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.35  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.35  #
% 0.16/0.35  # Preprocessing time       : 0.028 s
% 0.16/0.35  # Presaturation interreduction done
% 0.16/0.35  
% 0.16/0.35  # Proof found!
% 0.16/0.35  # SZS status Theorem
% 0.16/0.35  # SZS output start CNFRefutation
% 0.16/0.35  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.16/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.16/0.35  fof(t75_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 0.16/0.35  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.16/0.35  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.16/0.35  fof(t60_relat_1, conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.16/0.35  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.16/0.35  fof(c_0_7, plain, ![X8, X9, X10]:(((r2_hidden(X8,X9)|~r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))))&(X8!=X10|~r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10)))))&(~r2_hidden(X8,X9)|X8=X10|r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.16/0.35  fof(c_0_8, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.16/0.35  cnf(c_0_9, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.35  cnf(c_0_10, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.35  fof(c_0_11, plain, ![X11, X12, X13]:((k4_xboole_0(X11,k2_tarski(X12,X13))!=k1_xboole_0|(X11=k1_xboole_0|X11=k1_tarski(X12)|X11=k1_tarski(X13)|X11=k2_tarski(X12,X13)))&((((X11!=k1_xboole_0|k4_xboole_0(X11,k2_tarski(X12,X13))=k1_xboole_0)&(X11!=k1_tarski(X12)|k4_xboole_0(X11,k2_tarski(X12,X13))=k1_xboole_0))&(X11!=k1_tarski(X13)|k4_xboole_0(X11,k2_tarski(X12,X13))=k1_xboole_0))&(X11!=k2_tarski(X12,X13)|k4_xboole_0(X11,k2_tarski(X12,X13))=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_zfmisc_1])])])).
% 0.16/0.35  cnf(c_0_12, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.16/0.35  cnf(c_0_13, plain, (k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.35  fof(c_0_14, plain, ![X14, X15, X16, X18, X19, X20, X21, X23]:(((~r2_hidden(X16,X15)|r2_hidden(k4_tarski(X16,esk2_3(X14,X15,X16)),X14)|X15!=k1_relat_1(X14))&(~r2_hidden(k4_tarski(X18,X19),X14)|r2_hidden(X18,X15)|X15!=k1_relat_1(X14)))&((~r2_hidden(esk3_2(X20,X21),X21)|~r2_hidden(k4_tarski(esk3_2(X20,X21),X23),X20)|X21=k1_relat_1(X20))&(r2_hidden(esk3_2(X20,X21),X21)|r2_hidden(k4_tarski(esk3_2(X20,X21),esk4_2(X20,X21)),X20)|X21=k1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.16/0.35  cnf(c_0_15, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_12])).
% 0.16/0.35  cnf(c_0_16, plain, (k4_xboole_0(k1_xboole_0,k2_tarski(X1,X2))=k1_xboole_0), inference(er,[status(thm)],[c_0_13])).
% 0.16/0.35  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.35  fof(c_0_18, plain, ![X25, X26, X27, X29, X30, X31, X32, X34]:(((~r2_hidden(X27,X26)|r2_hidden(k4_tarski(esk5_3(X25,X26,X27),X27),X25)|X26!=k2_relat_1(X25))&(~r2_hidden(k4_tarski(X30,X29),X25)|r2_hidden(X29,X26)|X26!=k2_relat_1(X25)))&((~r2_hidden(esk6_2(X31,X32),X32)|~r2_hidden(k4_tarski(X34,esk6_2(X31,X32)),X31)|X32=k2_relat_1(X31))&(r2_hidden(esk6_2(X31,X32),X32)|r2_hidden(k4_tarski(esk7_2(X31,X32),esk6_2(X31,X32)),X31)|X32=k2_relat_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.16/0.35  fof(c_0_19, negated_conjecture, ~((k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_relat_1])).
% 0.16/0.35  cnf(c_0_20, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.16/0.35  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 0.16/0.35  fof(c_0_22, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.16/0.35  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.35  fof(c_0_24, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(fof_nnf,[status(thm)],[c_0_19])).
% 0.16/0.35  cnf(c_0_25, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.16/0.35  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.16/0.35  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_23])).
% 0.16/0.35  cnf(c_0_28, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.16/0.35  cnf(c_0_29, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.16/0.35  cnf(c_0_30, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_20, c_0_27])).
% 0.16/0.35  cnf(c_0_31, negated_conjecture, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])])).
% 0.16/0.35  cnf(c_0_32, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_31]), ['proof']).
% 0.16/0.35  # SZS output end CNFRefutation
% 0.16/0.35  # Proof object total steps             : 33
% 0.16/0.35  # Proof object clause steps            : 18
% 0.16/0.35  # Proof object formula steps           : 15
% 0.16/0.35  # Proof object conjectures             : 5
% 0.16/0.35  # Proof object clause conjectures      : 2
% 0.16/0.35  # Proof object formula conjectures     : 3
% 0.16/0.35  # Proof object initial clauses used    : 7
% 0.16/0.35  # Proof object initial formulas used   : 7
% 0.16/0.35  # Proof object generating inferences   : 5
% 0.16/0.35  # Proof object simplifying inferences  : 8
% 0.16/0.35  # Training examples: 0 positive, 0 negative
% 0.16/0.35  # Parsed axioms                        : 7
% 0.16/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.35  # Initial clauses                      : 19
% 0.16/0.35  # Removed in clause preprocessing      : 1
% 0.16/0.35  # Initial clauses in saturation        : 18
% 0.16/0.35  # Processed clauses                    : 53
% 0.16/0.35  # ...of these trivial                  : 0
% 0.16/0.35  # ...subsumed                          : 6
% 0.16/0.35  # ...remaining for further processing  : 47
% 0.16/0.35  # Other redundant clauses eliminated   : 9
% 0.16/0.35  # Clauses deleted for lack of memory   : 0
% 0.16/0.35  # Backward-subsumed                    : 0
% 0.16/0.35  # Backward-rewritten                   : 2
% 0.16/0.35  # Generated clauses                    : 37
% 0.16/0.35  # ...of the previous two non-trivial   : 33
% 0.16/0.35  # Contextual simplify-reflections      : 0
% 0.16/0.35  # Paramodulations                      : 28
% 0.16/0.35  # Factorizations                       : 0
% 0.16/0.35  # Equation resolutions                 : 9
% 0.16/0.35  # Propositional unsat checks           : 0
% 0.16/0.35  #    Propositional check models        : 0
% 0.16/0.35  #    Propositional check unsatisfiable : 0
% 0.16/0.35  #    Propositional clauses             : 0
% 0.16/0.35  #    Propositional clauses after purity: 0
% 0.16/0.35  #    Propositional unsat core size     : 0
% 0.16/0.35  #    Propositional preprocessing time  : 0.000
% 0.16/0.35  #    Propositional encoding time       : 0.000
% 0.16/0.35  #    Propositional solver time         : 0.000
% 0.16/0.35  #    Success case prop preproc time    : 0.000
% 0.16/0.35  #    Success case prop encoding time   : 0.000
% 0.16/0.35  #    Success case prop solver time     : 0.000
% 0.16/0.35  # Current number of processed clauses  : 18
% 0.16/0.35  #    Positive orientable unit clauses  : 5
% 0.16/0.35  #    Positive unorientable unit clauses: 0
% 0.16/0.35  #    Negative unit clauses             : 4
% 0.16/0.35  #    Non-unit-clauses                  : 9
% 0.16/0.35  # Current number of unprocessed clauses: 16
% 0.16/0.35  # ...number of literals in the above   : 41
% 0.16/0.35  # Current number of archived formulas  : 0
% 0.16/0.35  # Current number of archived clauses   : 21
% 0.16/0.35  # Clause-clause subsumption calls (NU) : 22
% 0.16/0.35  # Rec. Clause-clause subsumption calls : 22
% 0.16/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.16/0.35  # Unit Clause-clause subsumption calls : 1
% 0.16/0.35  # Rewrite failures with RHS unbound    : 0
% 0.16/0.35  # BW rewrite match attempts            : 7
% 0.16/0.35  # BW rewrite match successes           : 1
% 0.16/0.35  # Condensation attempts                : 0
% 0.16/0.35  # Condensation successes               : 0
% 0.16/0.35  # Termbank termtop insertions          : 1697
% 0.16/0.35  
% 0.16/0.35  # -------------------------------------------------
% 0.16/0.35  # User time                : 0.029 s
% 0.16/0.35  # System time              : 0.003 s
% 0.16/0.35  # Total time               : 0.032 s
% 0.16/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
