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
% DateTime   : Thu Dec  3 10:43:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 262 expanded)
%              Number of clauses        :   31 ( 119 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 877 expanded)
%              Number of equality atoms :   66 ( 271 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(t61_xboole_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(c_0_10,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | ~ r2_xboole_0(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

fof(c_0_11,plain,(
    ! [X25] :
      ( X25 = k1_xboole_0
      | r2_xboole_0(k1_xboole_0,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X18)
        | r2_hidden(X16,X17)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_14,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X44,X45,X46,X47] :
      ( ( r2_hidden(X44,X46)
        | ~ r2_hidden(k4_tarski(X44,X45),k2_zfmisc_1(X46,X47)) )
      & ( r2_hidden(X45,X47)
        | ~ r2_hidden(k4_tarski(X44,X45),k2_zfmisc_1(X46,X47)) )
      & ( ~ r2_hidden(X44,X46)
        | ~ r2_hidden(X45,X47)
        | r2_hidden(k4_tarski(X44,X45),k2_zfmisc_1(X46,X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_26,negated_conjecture,
    ( ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( esk9_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
      | esk8_0 = k1_xboole_0
      | esk9_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_33,plain,(
    ! [X19] :
      ( X19 = k1_xboole_0
      | r2_hidden(esk2_1(X19),X19) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_34,plain,(
    ! [X27,X28,X29,X30,X33,X34,X35,X36,X37,X38,X40,X41] :
      ( ( r2_hidden(esk3_4(X27,X28,X29,X30),X27)
        | ~ r2_hidden(X30,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( r2_hidden(esk4_4(X27,X28,X29,X30),X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( X30 = k4_tarski(esk3_4(X27,X28,X29,X30),esk4_4(X27,X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( ~ r2_hidden(X34,X27)
        | ~ r2_hidden(X35,X28)
        | X33 != k4_tarski(X34,X35)
        | r2_hidden(X33,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( ~ r2_hidden(esk5_3(X36,X37,X38),X38)
        | ~ r2_hidden(X40,X36)
        | ~ r2_hidden(X41,X37)
        | esk5_3(X36,X37,X38) != k4_tarski(X40,X41)
        | X38 = k2_zfmisc_1(X36,X37) )
      & ( r2_hidden(esk6_3(X36,X37,X38),X36)
        | r2_hidden(esk5_3(X36,X37,X38),X38)
        | X38 = k2_zfmisc_1(X36,X37) )
      & ( r2_hidden(esk7_3(X36,X37,X38),X37)
        | r2_hidden(esk5_3(X36,X37,X38),X38)
        | X38 = k2_zfmisc_1(X36,X37) )
      & ( esk5_3(X36,X37,X38) = k4_tarski(esk6_3(X36,X37,X38),esk7_3(X36,X37,X38))
        | r2_hidden(esk5_3(X36,X37,X38),X38)
        | X38 = k2_zfmisc_1(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_29]),c_0_32]),c_0_32])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( X1 != k2_zfmisc_1(X2,k1_xboole_0)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( X1 != k2_zfmisc_1(k1_xboole_0,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | k2_zfmisc_1(esk8_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_36])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.20/0.38  fof(t61_xboole_1, axiom, ![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 0.20/0.38  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.20/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.38  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.38  fof(t106_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 0.20/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.38  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.38  fof(c_0_10, plain, ![X23, X24]:(~r1_tarski(X23,X24)|~r2_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.20/0.38  fof(c_0_11, plain, ![X25]:(X25=k1_xboole_0|r2_xboole_0(k1_xboole_0,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).
% 0.20/0.38  fof(c_0_12, plain, ![X16, X17, X18]:(((~r2_hidden(X16,X17)|~r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18)))&(r2_hidden(X16,X17)|r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18))))&((~r2_hidden(X16,X17)|r2_hidden(X16,X18)|r2_hidden(X16,k5_xboole_0(X17,X18)))&(~r2_hidden(X16,X18)|r2_hidden(X16,X17)|r2_hidden(X16,k5_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.38  cnf(c_0_14, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (X1=k1_xboole_0|r2_xboole_0(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_16, plain, ![X21, X22]:r1_tarski(k3_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.38  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_18, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.20/0.38  fof(c_0_20, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.38  cnf(c_0_21, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  fof(c_0_25, plain, ![X44, X45, X46, X47]:(((r2_hidden(X44,X46)|~r2_hidden(k4_tarski(X44,X45),k2_zfmisc_1(X46,X47)))&(r2_hidden(X45,X47)|~r2_hidden(k4_tarski(X44,X45),k2_zfmisc_1(X46,X47))))&(~r2_hidden(X44,X46)|~r2_hidden(X45,X47)|r2_hidden(k4_tarski(X44,X45),k2_zfmisc_1(X46,X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_26, negated_conjecture, (((esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0)&(esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0))&(k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|(esk8_0=k1_xboole_0|esk9_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 0.20/0.38  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_28, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_29, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_24])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_32, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.20/0.38  fof(c_0_33, plain, ![X19]:(X19=k1_xboole_0|r2_hidden(esk2_1(X19),X19)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.38  fof(c_0_34, plain, ![X27, X28, X29, X30, X33, X34, X35, X36, X37, X38, X40, X41]:(((((r2_hidden(esk3_4(X27,X28,X29,X30),X27)|~r2_hidden(X30,X29)|X29!=k2_zfmisc_1(X27,X28))&(r2_hidden(esk4_4(X27,X28,X29,X30),X28)|~r2_hidden(X30,X29)|X29!=k2_zfmisc_1(X27,X28)))&(X30=k4_tarski(esk3_4(X27,X28,X29,X30),esk4_4(X27,X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k2_zfmisc_1(X27,X28)))&(~r2_hidden(X34,X27)|~r2_hidden(X35,X28)|X33!=k4_tarski(X34,X35)|r2_hidden(X33,X29)|X29!=k2_zfmisc_1(X27,X28)))&((~r2_hidden(esk5_3(X36,X37,X38),X38)|(~r2_hidden(X40,X36)|~r2_hidden(X41,X37)|esk5_3(X36,X37,X38)!=k4_tarski(X40,X41))|X38=k2_zfmisc_1(X36,X37))&(((r2_hidden(esk6_3(X36,X37,X38),X36)|r2_hidden(esk5_3(X36,X37,X38),X38)|X38=k2_zfmisc_1(X36,X37))&(r2_hidden(esk7_3(X36,X37,X38),X37)|r2_hidden(esk5_3(X36,X37,X38),X38)|X38=k2_zfmisc_1(X36,X37)))&(esk5_3(X36,X37,X38)=k4_tarski(esk6_3(X36,X37,X38),esk7_3(X36,X37,X38))|r2_hidden(esk5_3(X36,X37,X38),X38)|X38=k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_29]), c_0_32]), c_0_32])).
% 0.20/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_37, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (esk9_0=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_39, plain, (X1!=k2_zfmisc_1(X2,k1_xboole_0)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_37])).
% 0.20/0.38  cnf(c_0_40, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_36])).
% 0.20/0.38  cnf(c_0_43, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_44, plain, (X1!=k2_zfmisc_1(k1_xboole_0,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_40])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (esk8_0=k1_xboole_0|k2_zfmisc_1(esk8_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  cnf(c_0_46, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_36])).
% 0.20/0.38  cnf(c_0_47, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.20/0.38  cnf(c_0_50, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_36])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_49])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 52
% 0.20/0.38  # Proof object clause steps            : 31
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 12
% 0.20/0.38  # Proof object clause conjectures      : 9
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 14
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 15
% 0.20/0.38  # Proof object simplifying inferences  : 11
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 29
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 29
% 0.20/0.38  # Processed clauses                    : 102
% 0.20/0.38  # ...of these trivial                  : 3
% 0.20/0.38  # ...subsumed                          : 15
% 0.20/0.38  # ...remaining for further processing  : 84
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 4
% 0.20/0.38  # Backward-rewritten                   : 16
% 0.20/0.38  # Generated clauses                    : 142
% 0.20/0.38  # ...of the previous two non-trivial   : 126
% 0.20/0.38  # Contextual simplify-reflections      : 3
% 0.20/0.38  # Paramodulations                      : 136
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 6
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 35
% 0.20/0.38  #    Positive orientable unit clauses  : 8
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 26
% 0.20/0.38  # Current number of unprocessed clauses: 76
% 0.20/0.38  # ...number of literals in the above   : 236
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 49
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 435
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 290
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.38  # Unit Clause-clause subsumption calls : 15
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 5
% 0.20/0.38  # BW rewrite match successes           : 5
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3403
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
