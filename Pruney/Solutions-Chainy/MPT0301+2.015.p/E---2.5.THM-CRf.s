%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:26 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 957 expanded)
%              Number of clauses        :   38 ( 462 expanded)
%              Number of leaves         :    7 ( 245 expanded)
%              Depth                    :   21
%              Number of atoms          :  164 (3720 expanded)
%              Number of equality atoms :   74 ( 980 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X15)
        | r2_hidden(X13,X14)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_8,plain,(
    ! [X20] : k5_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X19] : r1_tarski(k1_xboole_0,X19) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X21,X22,X23,X24,X27,X28,X29,X30,X31,X32,X34,X35] :
      ( ( r2_hidden(esk3_4(X21,X22,X23,X24),X21)
        | ~ r2_hidden(X24,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( r2_hidden(esk4_4(X21,X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( X24 = k4_tarski(esk3_4(X21,X22,X23,X24),esk4_4(X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( ~ r2_hidden(X28,X21)
        | ~ r2_hidden(X29,X22)
        | X27 != k4_tarski(X28,X29)
        | r2_hidden(X27,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( ~ r2_hidden(esk5_3(X30,X31,X32),X32)
        | ~ r2_hidden(X34,X30)
        | ~ r2_hidden(X35,X31)
        | esk5_3(X30,X31,X32) != k4_tarski(X34,X35)
        | X32 = k2_zfmisc_1(X30,X31) )
      & ( r2_hidden(esk6_3(X30,X31,X32),X30)
        | r2_hidden(esk5_3(X30,X31,X32),X32)
        | X32 = k2_zfmisc_1(X30,X31) )
      & ( r2_hidden(esk7_3(X30,X31,X32),X31)
        | r2_hidden(esk5_3(X30,X31,X32),X32)
        | X32 = k2_zfmisc_1(X30,X31) )
      & ( esk5_3(X30,X31,X32) = k4_tarski(esk6_3(X30,X31,X32),esk7_3(X30,X31,X32))
        | r2_hidden(esk5_3(X30,X31,X32),X32)
        | X32 = k2_zfmisc_1(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( X1 != k2_zfmisc_1(k1_xboole_0,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ( ~ r2_hidden(esk2_2(X16,X17),X16)
        | ~ r2_hidden(esk2_2(X16,X17),X17)
        | X16 = X17 )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r2_hidden(esk2_2(X16,X17),X17)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_22,plain,
    ( X1 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_26,plain,
    ( X1 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3),X4)
    | ~ r2_hidden(X5,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_28,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_29,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_31,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | X3 != k1_xboole_0
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,negated_conjecture,
    ( ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( esk9_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
      | esk8_0 = k1_xboole_0
      | esk9_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).

cnf(c_0_33,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_34,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_37,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( X1 != k4_tarski(X2,X3)
    | X4 != k1_xboole_0
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( X1 != k4_tarski(X2,esk2_2(k1_xboole_0,esk9_0))
    | X3 != k1_xboole_0
    | ~ r2_hidden(X2,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_25]),c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,esk8_0) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_48]),c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( X1 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_43])).

cnf(c_0_52,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.21/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.039 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.21/0.44  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.44  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.21/0.44  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.21/0.44  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.44  fof(c_0_7, plain, ![X13, X14, X15]:(((~r2_hidden(X13,X14)|~r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15)))&(r2_hidden(X13,X14)|r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15))))&((~r2_hidden(X13,X14)|r2_hidden(X13,X15)|r2_hidden(X13,k5_xboole_0(X14,X15)))&(~r2_hidden(X13,X15)|r2_hidden(X13,X14)|r2_hidden(X13,k5_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.21/0.44  fof(c_0_8, plain, ![X20]:k5_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.44  fof(c_0_9, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.44  fof(c_0_10, plain, ![X19]:r1_tarski(k1_xboole_0,X19), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.44  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.44  cnf(c_0_12, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.44  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.44  cnf(c_0_14, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.44  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.44  fof(c_0_16, plain, ![X21, X22, X23, X24, X27, X28, X29, X30, X31, X32, X34, X35]:(((((r2_hidden(esk3_4(X21,X22,X23,X24),X21)|~r2_hidden(X24,X23)|X23!=k2_zfmisc_1(X21,X22))&(r2_hidden(esk4_4(X21,X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k2_zfmisc_1(X21,X22)))&(X24=k4_tarski(esk3_4(X21,X22,X23,X24),esk4_4(X21,X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k2_zfmisc_1(X21,X22)))&(~r2_hidden(X28,X21)|~r2_hidden(X29,X22)|X27!=k4_tarski(X28,X29)|r2_hidden(X27,X23)|X23!=k2_zfmisc_1(X21,X22)))&((~r2_hidden(esk5_3(X30,X31,X32),X32)|(~r2_hidden(X34,X30)|~r2_hidden(X35,X31)|esk5_3(X30,X31,X32)!=k4_tarski(X34,X35))|X32=k2_zfmisc_1(X30,X31))&(((r2_hidden(esk6_3(X30,X31,X32),X30)|r2_hidden(esk5_3(X30,X31,X32),X32)|X32=k2_zfmisc_1(X30,X31))&(r2_hidden(esk7_3(X30,X31,X32),X31)|r2_hidden(esk5_3(X30,X31,X32),X32)|X32=k2_zfmisc_1(X30,X31)))&(esk5_3(X30,X31,X32)=k4_tarski(esk6_3(X30,X31,X32),esk7_3(X30,X31,X32))|r2_hidden(esk5_3(X30,X31,X32),X32)|X32=k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.21/0.44  cnf(c_0_17, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.21/0.44  cnf(c_0_18, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_19, plain, (X1!=k2_zfmisc_1(k1_xboole_0,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.44  cnf(c_0_20, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.21/0.44  fof(c_0_21, plain, ![X16, X17]:((~r2_hidden(esk2_2(X16,X17),X16)|~r2_hidden(esk2_2(X16,X17),X17)|X16=X17)&(r2_hidden(esk2_2(X16,X17),X16)|r2_hidden(esk2_2(X16,X17),X17)|X16=X17)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.21/0.44  cnf(c_0_22, plain, (X1!=k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.21/0.44  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.44  cnf(c_0_24, plain, (~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3))), inference(er,[status(thm)],[c_0_22])).
% 0.21/0.44  cnf(c_0_25, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 0.21/0.44  cnf(c_0_26, plain, (X1!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3),X4)|~r2_hidden(X5,X1)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.21/0.44  cnf(c_0_27, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.21/0.44  cnf(c_0_28, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_27])).
% 0.21/0.44  cnf(c_0_29, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  fof(c_0_30, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.21/0.44  cnf(c_0_31, plain, (X1!=k2_zfmisc_1(X2,X3)|X3!=k1_xboole_0|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.44  fof(c_0_32, negated_conjecture, (((esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0)&(esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0))&(k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|(esk8_0=k1_xboole_0|esk9_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).
% 0.21/0.44  cnf(c_0_33, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X3,X1))), inference(er,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_34, plain, (X1!=k2_zfmisc_1(X2,X3)|X2!=k1_xboole_0|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.21/0.44  cnf(c_0_35, negated_conjecture, (esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.44  cnf(c_0_36, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 0.21/0.44  cnf(c_0_37, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X1,X3))), inference(er,[status(thm)],[c_0_34])).
% 0.21/0.44  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.44  cnf(c_0_39, negated_conjecture, (esk9_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.44  cnf(c_0_40, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.44  cnf(c_0_41, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 0.21/0.44  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.44  cnf(c_0_43, negated_conjecture, (esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.44  cnf(c_0_44, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.44  cnf(c_0_46, negated_conjecture, (X1!=k4_tarski(X2,X3)|X4!=k1_xboole_0|~r2_hidden(X3,esk9_0)|~r2_hidden(X2,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_28])).
% 0.21/0.44  cnf(c_0_47, negated_conjecture, (X1!=k4_tarski(X2,esk2_2(k1_xboole_0,esk9_0))|X3!=k1_xboole_0|~r2_hidden(X2,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_25]), c_0_39])).
% 0.21/0.44  cnf(c_0_48, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_49, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,esk8_0)), inference(er,[status(thm)],[c_0_47])).
% 0.21/0.44  cnf(c_0_50, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_48]), c_0_27])).
% 0.21/0.44  cnf(c_0_51, negated_conjecture, (X1!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_43])).
% 0.21/0.44  cnf(c_0_52, plain, ($false), inference(sr,[status(thm)],[c_0_27, c_0_51]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 53
% 0.21/0.44  # Proof object clause steps            : 38
% 0.21/0.44  # Proof object formula steps           : 15
% 0.21/0.44  # Proof object conjectures             : 14
% 0.21/0.44  # Proof object clause conjectures      : 11
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 12
% 0.21/0.44  # Proof object initial formulas used   : 7
% 0.21/0.44  # Proof object generating inferences   : 22
% 0.21/0.44  # Proof object simplifying inferences  : 11
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 7
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 22
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 22
% 0.21/0.44  # Processed clauses                    : 697
% 0.21/0.44  # ...of these trivial                  : 4
% 0.21/0.44  # ...subsumed                          : 509
% 0.21/0.44  # ...remaining for further processing  : 184
% 0.21/0.44  # Other redundant clauses eliminated   : 1
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 2
% 0.21/0.44  # Backward-rewritten                   : 34
% 0.21/0.44  # Generated clauses                    : 1933
% 0.21/0.44  # ...of the previous two non-trivial   : 1628
% 0.21/0.44  # Contextual simplify-reflections      : 2
% 0.21/0.44  # Paramodulations                      : 1859
% 0.21/0.44  # Factorizations                       : 24
% 0.21/0.44  # Equation resolutions                 : 38
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 114
% 0.21/0.44  #    Positive orientable unit clauses  : 3
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 4
% 0.21/0.44  #    Non-unit-clauses                  : 107
% 0.21/0.44  # Current number of unprocessed clauses: 888
% 0.21/0.44  # ...number of literals in the above   : 3427
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 70
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 2095
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 1505
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 324
% 0.21/0.44  # Unit Clause-clause subsumption calls : 147
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 16
% 0.21/0.44  # BW rewrite match successes           : 9
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 20496
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.096 s
% 0.21/0.44  # System time              : 0.002 s
% 0.21/0.44  # Total time               : 0.098 s
% 0.21/0.44  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
