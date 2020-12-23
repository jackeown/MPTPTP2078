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
% DateTime   : Thu Dec  3 10:43:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 588 expanded)
%              Number of clauses        :   33 ( 273 expanded)
%              Number of leaves         :    5 ( 155 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 (2069 expanded)
%              Number of equality atoms :   64 ( 769 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_7,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X15,X16,X17,X18,X21,X22,X23,X24,X25,X26,X28,X29] :
      ( ( r2_hidden(esk2_4(X15,X16,X17,X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( r2_hidden(esk3_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( X18 = k4_tarski(esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(X22,X15)
        | ~ r2_hidden(X23,X16)
        | X21 != k4_tarski(X22,X23)
        | r2_hidden(X21,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(esk4_3(X24,X25,X26),X26)
        | ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X29,X25)
        | esk4_3(X24,X25,X26) != k4_tarski(X28,X29)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X24)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk6_3(X24,X25,X26),X25)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( esk4_3(X24,X25,X26) = k4_tarski(esk5_3(X24,X25,X26),esk6_3(X24,X25,X26))
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 != k2_zfmisc_1(k1_xboole_0,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( X1 = k2_zfmisc_1(k1_xboole_0,X2)
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_15])).

cnf(c_0_18,plain,
    ( X1 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_20,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_23,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | X3 != k1_xboole_0
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,negated_conjecture,
    ( ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
      | esk7_0 = k1_xboole_0
      | esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])).

cnf(c_0_25,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_27,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.027 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.40  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.13/0.40  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.40  fof(c_0_5, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_6, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.40  fof(c_0_7, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.40  cnf(c_0_8, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_9, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_10, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  fof(c_0_11, plain, ![X15, X16, X17, X18, X21, X22, X23, X24, X25, X26, X28, X29]:(((((r2_hidden(esk2_4(X15,X16,X17,X18),X15)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16))&(r2_hidden(esk3_4(X15,X16,X17,X18),X16)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(X18=k4_tarski(esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(~r2_hidden(X22,X15)|~r2_hidden(X23,X16)|X21!=k4_tarski(X22,X23)|r2_hidden(X21,X17)|X17!=k2_zfmisc_1(X15,X16)))&((~r2_hidden(esk4_3(X24,X25,X26),X26)|(~r2_hidden(X28,X24)|~r2_hidden(X29,X25)|esk4_3(X24,X25,X26)!=k4_tarski(X28,X29))|X26=k2_zfmisc_1(X24,X25))&(((r2_hidden(esk5_3(X24,X25,X26),X24)|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))&(r2_hidden(esk6_3(X24,X25,X26),X25)|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25)))&(esk4_3(X24,X25,X26)=k4_tarski(esk5_3(X24,X25,X26),esk6_3(X24,X25,X26))|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.13/0.40  cnf(c_0_12, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_13, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_14, plain, (X1!=k2_zfmisc_1(k1_xboole_0,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.40  cnf(c_0_15, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_16, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(er,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_17, plain, (X1=k2_zfmisc_1(k1_xboole_0,X2)|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_12, c_0_15])).
% 0.13/0.40  cnf(c_0_18, plain, (X1!=k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 0.13/0.40  cnf(c_0_19, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_17])).
% 0.13/0.40  cnf(c_0_20, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.13/0.40  cnf(c_0_21, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.13/0.40  cnf(c_0_23, plain, (X1!=k2_zfmisc_1(X2,X3)|X3!=k1_xboole_0|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  fof(c_0_24, negated_conjecture, (((esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0)&(esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0))&(k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|(esk7_0=k1_xboole_0|esk8_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])).
% 0.13/0.40  cnf(c_0_25, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X3,X1))), inference(er,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_17, c_0_19])).
% 0.13/0.40  cnf(c_0_27, plain, (X1!=k2_zfmisc_1(X2,X3)|X2!=k1_xboole_0|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_20, c_0_13])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_29, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.40  cnf(c_0_30, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X1,X3))), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_31, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_35, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.13/0.40  cnf(c_0_36, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|X1!=k4_tarski(X4,X5)|~r2_hidden(X5,X3)|~r2_hidden(X4,X2)), inference(er,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.40  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (~r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_12])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_33])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_38]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 44
% 0.13/0.40  # Proof object clause steps            : 33
% 0.13/0.40  # Proof object formula steps           : 11
% 0.13/0.40  # Proof object conjectures             : 13
% 0.13/0.40  # Proof object clause conjectures      : 10
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 10
% 0.13/0.40  # Proof object initial formulas used   : 5
% 0.13/0.40  # Proof object generating inferences   : 19
% 0.13/0.40  # Proof object simplifying inferences  : 10
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 5
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 15
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 15
% 0.13/0.40  # Processed clauses                    : 462
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 352
% 0.13/0.40  # ...remaining for further processing  : 110
% 0.13/0.40  # Other redundant clauses eliminated   : 1
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 2
% 0.13/0.40  # Backward-rewritten                   : 15
% 0.13/0.40  # Generated clauses                    : 1225
% 0.13/0.40  # ...of the previous two non-trivial   : 1172
% 0.13/0.40  # Contextual simplify-reflections      : 1
% 0.13/0.40  # Paramodulations                      : 1195
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 28
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 76
% 0.13/0.40  #    Positive orientable unit clauses  : 5
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 4
% 0.13/0.40  #    Non-unit-clauses                  : 67
% 0.13/0.40  # Current number of unprocessed clauses: 706
% 0.13/0.40  # ...number of literals in the above   : 2874
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 34
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 898
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 752
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 217
% 0.13/0.40  # Unit Clause-clause subsumption calls : 28
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 5
% 0.13/0.40  # BW rewrite match successes           : 5
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 9538
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.047 s
% 0.13/0.40  # System time              : 0.002 s
% 0.13/0.40  # Total time               : 0.050 s
% 0.13/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
