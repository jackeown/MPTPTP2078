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
% DateTime   : Thu Dec  3 10:43:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 357 expanded)
%              Number of clauses        :   33 ( 166 expanded)
%              Number of leaves         :    8 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  153 ( 966 expanded)
%              Number of equality atoms :   78 ( 440 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

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

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X16,X17] : r1_xboole_0(k4_xboole_0(X16,X17),X17) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_11,plain,(
    ! [X15] : k4_xboole_0(k1_xboole_0,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X35,X36,X37,X39,X40,X41,X42,X44] :
      ( ( r2_hidden(X37,esk7_3(X35,X36,X37))
        | ~ r2_hidden(X37,X36)
        | X36 != k3_tarski(X35) )
      & ( r2_hidden(esk7_3(X35,X36,X37),X35)
        | ~ r2_hidden(X37,X36)
        | X36 != k3_tarski(X35) )
      & ( ~ r2_hidden(X39,X40)
        | ~ r2_hidden(X40,X35)
        | r2_hidden(X39,X36)
        | X36 != k3_tarski(X35) )
      & ( ~ r2_hidden(esk8_2(X41,X42),X42)
        | ~ r2_hidden(esk8_2(X41,X42),X44)
        | ~ r2_hidden(X44,X41)
        | X42 = k3_tarski(X41) )
      & ( r2_hidden(esk8_2(X41,X42),esk9_2(X41,X42))
        | r2_hidden(esk8_2(X41,X42),X42)
        | X42 = k3_tarski(X41) )
      & ( r2_hidden(esk9_2(X41,X42),X41)
        | r2_hidden(esk8_2(X41,X42),X42)
        | X42 = k3_tarski(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_15]),c_0_17])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

fof(c_0_22,plain,(
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

cnf(c_0_23,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_26,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(esk9_2(X1,X2),X1)
    | r2_hidden(esk8_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,negated_conjecture,
    ( ( esk10_0 != k1_xboole_0
      | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 )
    & ( esk11_0 != k1_xboole_0
      | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk10_0,esk11_0) = k1_xboole_0
      | esk10_0 = k1_xboole_0
      | esk11_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])])).

cnf(c_0_30,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk8_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_27]),c_0_21])).

cnf(c_0_32,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | X3 != k1_xboole_0
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( esk10_0 != k1_xboole_0
    | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,esk11_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( esk11_0 != k1_xboole_0
    | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,esk11_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,esk11_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( X1 != k4_tarski(X2,X3)
    | X4 != k1_xboole_0
    | ~ r2_hidden(X3,esk11_0)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( X1 != k4_tarski(X2,esk8_2(k1_xboole_0,esk11_0))
    | X3 != k1_xboole_0
    | ~ r2_hidden(X2,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,esk10_0) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( X1 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_37])).

cnf(c_0_48,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_21,c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.55  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.55  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.55  #
% 0.19/0.55  # Preprocessing time       : 0.027 s
% 0.19/0.55  # Presaturation interreduction done
% 0.19/0.55  
% 0.19/0.55  # Proof found!
% 0.19/0.55  # SZS status Theorem
% 0.19/0.55  # SZS output start CNFRefutation
% 0.19/0.55  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.55  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.55  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.55  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.55  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.56  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.19/0.56  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.56  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.56  fof(c_0_8, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.56  fof(c_0_9, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.56  fof(c_0_10, plain, ![X16, X17]:r1_xboole_0(k4_xboole_0(X16,X17),X17), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.56  fof(c_0_11, plain, ![X15]:k4_xboole_0(k1_xboole_0,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.56  cnf(c_0_12, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.56  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.56  cnf(c_0_14, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.56  cnf(c_0_15, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.56  cnf(c_0_16, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.56  cnf(c_0_17, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.56  fof(c_0_18, plain, ![X35, X36, X37, X39, X40, X41, X42, X44]:((((r2_hidden(X37,esk7_3(X35,X36,X37))|~r2_hidden(X37,X36)|X36!=k3_tarski(X35))&(r2_hidden(esk7_3(X35,X36,X37),X35)|~r2_hidden(X37,X36)|X36!=k3_tarski(X35)))&(~r2_hidden(X39,X40)|~r2_hidden(X40,X35)|r2_hidden(X39,X36)|X36!=k3_tarski(X35)))&((~r2_hidden(esk8_2(X41,X42),X42)|(~r2_hidden(esk8_2(X41,X42),X44)|~r2_hidden(X44,X41))|X42=k3_tarski(X41))&((r2_hidden(esk8_2(X41,X42),esk9_2(X41,X42))|r2_hidden(esk8_2(X41,X42),X42)|X42=k3_tarski(X41))&(r2_hidden(esk9_2(X41,X42),X41)|r2_hidden(esk8_2(X41,X42),X42)|X42=k3_tarski(X41))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.56  cnf(c_0_19, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_15]), c_0_15]), c_0_17])])).
% 0.19/0.56  cnf(c_0_20, plain, (r2_hidden(esk7_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.56  cnf(c_0_21, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.19/0.56  fof(c_0_22, plain, ![X18, X19, X20, X21, X24, X25, X26, X27, X28, X29, X31, X32]:(((((r2_hidden(esk2_4(X18,X19,X20,X21),X18)|~r2_hidden(X21,X20)|X20!=k2_zfmisc_1(X18,X19))&(r2_hidden(esk3_4(X18,X19,X20,X21),X19)|~r2_hidden(X21,X20)|X20!=k2_zfmisc_1(X18,X19)))&(X21=k4_tarski(esk2_4(X18,X19,X20,X21),esk3_4(X18,X19,X20,X21))|~r2_hidden(X21,X20)|X20!=k2_zfmisc_1(X18,X19)))&(~r2_hidden(X25,X18)|~r2_hidden(X26,X19)|X24!=k4_tarski(X25,X26)|r2_hidden(X24,X20)|X20!=k2_zfmisc_1(X18,X19)))&((~r2_hidden(esk4_3(X27,X28,X29),X29)|(~r2_hidden(X31,X27)|~r2_hidden(X32,X28)|esk4_3(X27,X28,X29)!=k4_tarski(X31,X32))|X29=k2_zfmisc_1(X27,X28))&(((r2_hidden(esk5_3(X27,X28,X29),X27)|r2_hidden(esk4_3(X27,X28,X29),X29)|X29=k2_zfmisc_1(X27,X28))&(r2_hidden(esk6_3(X27,X28,X29),X28)|r2_hidden(esk4_3(X27,X28,X29),X29)|X29=k2_zfmisc_1(X27,X28)))&(esk4_3(X27,X28,X29)=k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29))|r2_hidden(esk4_3(X27,X28,X29),X29)|X29=k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.56  cnf(c_0_23, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.56  cnf(c_0_24, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.56  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.19/0.56  cnf(c_0_26, plain, (X1!=k2_zfmisc_1(X2,X3)|X2!=k1_xboole_0|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.56  cnf(c_0_27, plain, (r2_hidden(esk9_2(X1,X2),X1)|r2_hidden(esk8_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.56  cnf(c_0_28, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.56  fof(c_0_29, negated_conjecture, (((esk10_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0)&(esk11_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0))&(k2_zfmisc_1(esk10_0,esk11_0)=k1_xboole_0|(esk10_0=k1_xboole_0|esk11_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])])).
% 0.19/0.56  cnf(c_0_30, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X1,X3))), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.56  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(esk8_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_27]), c_0_21])).
% 0.19/0.56  cnf(c_0_32, plain, (X1!=k2_zfmisc_1(X2,X3)|X3!=k1_xboole_0|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_23, c_0_28])).
% 0.19/0.56  cnf(c_0_33, negated_conjecture, (esk10_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_34, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.56  cnf(c_0_35, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X3,X1))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.56  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(esk10_0,esk11_0)=k1_xboole_0|esk10_0=k1_xboole_0|esk11_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_37, negated_conjecture, (esk10_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.56  cnf(c_0_38, negated_conjecture, (esk11_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_39, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 0.19/0.56  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(esk10_0,esk11_0)=k1_xboole_0|esk11_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.56  cnf(c_0_41, negated_conjecture, (esk11_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.56  cnf(c_0_42, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.56  cnf(c_0_43, negated_conjecture, (k2_zfmisc_1(esk10_0,esk11_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.56  cnf(c_0_44, negated_conjecture, (X1!=k4_tarski(X2,X3)|X4!=k1_xboole_0|~r2_hidden(X3,esk11_0)|~r2_hidden(X2,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_23])).
% 0.19/0.56  cnf(c_0_45, negated_conjecture, (X1!=k4_tarski(X2,esk8_2(k1_xboole_0,esk11_0))|X3!=k1_xboole_0|~r2_hidden(X2,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_41])).
% 0.19/0.56  cnf(c_0_46, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,esk10_0)), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.56  cnf(c_0_47, negated_conjecture, (X1!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_37])).
% 0.19/0.56  cnf(c_0_48, plain, ($false), inference(sr,[status(thm)],[c_0_21, c_0_47]), ['proof']).
% 0.19/0.56  # SZS output end CNFRefutation
% 0.19/0.56  # Proof object total steps             : 49
% 0.19/0.56  # Proof object clause steps            : 33
% 0.19/0.56  # Proof object formula steps           : 16
% 0.19/0.56  # Proof object conjectures             : 14
% 0.19/0.56  # Proof object clause conjectures      : 11
% 0.19/0.56  # Proof object formula conjectures     : 3
% 0.19/0.56  # Proof object initial clauses used    : 13
% 0.19/0.56  # Proof object initial formulas used   : 8
% 0.19/0.56  # Proof object generating inferences   : 16
% 0.19/0.56  # Proof object simplifying inferences  : 12
% 0.19/0.56  # Training examples: 0 positive, 0 negative
% 0.19/0.56  # Parsed axioms                        : 8
% 0.19/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.56  # Initial clauses                      : 23
% 0.19/0.56  # Removed in clause preprocessing      : 1
% 0.19/0.56  # Initial clauses in saturation        : 22
% 0.19/0.56  # Processed clauses                    : 3898
% 0.19/0.56  # ...of these trivial                  : 28
% 0.19/0.56  # ...subsumed                          : 3425
% 0.19/0.56  # ...remaining for further processing  : 445
% 0.19/0.56  # Other redundant clauses eliminated   : 1
% 0.19/0.56  # Clauses deleted for lack of memory   : 0
% 0.19/0.56  # Backward-subsumed                    : 31
% 0.19/0.56  # Backward-rewritten                   : 8
% 0.19/0.56  # Generated clauses                    : 14767
% 0.19/0.56  # ...of the previous two non-trivial   : 12900
% 0.19/0.56  # Contextual simplify-reflections      : 11
% 0.19/0.56  # Paramodulations                      : 14593
% 0.19/0.56  # Factorizations                       : 0
% 0.19/0.56  # Equation resolutions                 : 163
% 0.19/0.56  # Propositional unsat checks           : 0
% 0.19/0.56  #    Propositional check models        : 0
% 0.19/0.56  #    Propositional check unsatisfiable : 0
% 0.19/0.56  #    Propositional clauses             : 0
% 0.19/0.56  #    Propositional clauses after purity: 0
% 0.19/0.56  #    Propositional unsat core size     : 0
% 0.19/0.56  #    Propositional preprocessing time  : 0.000
% 0.19/0.56  #    Propositional encoding time       : 0.000
% 0.19/0.56  #    Propositional solver time         : 0.000
% 0.19/0.56  #    Success case prop preproc time    : 0.000
% 0.19/0.56  #    Success case prop encoding time   : 0.000
% 0.19/0.56  #    Success case prop solver time     : 0.000
% 0.19/0.56  # Current number of processed clauses  : 373
% 0.19/0.56  #    Positive orientable unit clauses  : 2
% 0.19/0.56  #    Positive unorientable unit clauses: 0
% 0.19/0.56  #    Negative unit clauses             : 4
% 0.19/0.56  #    Non-unit-clauses                  : 367
% 0.19/0.56  # Current number of unprocessed clauses: 9022
% 0.19/0.56  # ...number of literals in the above   : 47595
% 0.19/0.56  # Current number of archived formulas  : 0
% 0.19/0.56  # Current number of archived clauses   : 73
% 0.19/0.56  # Clause-clause subsumption calls (NU) : 54124
% 0.19/0.56  # Rec. Clause-clause subsumption calls : 23467
% 0.19/0.56  # Non-unit clause-clause subsumptions  : 2359
% 0.19/0.56  # Unit Clause-clause subsumption calls : 295
% 0.19/0.56  # Rewrite failures with RHS unbound    : 0
% 0.19/0.56  # BW rewrite match attempts            : 3
% 0.19/0.56  # BW rewrite match successes           : 3
% 0.19/0.56  # Condensation attempts                : 0
% 0.19/0.56  # Condensation successes               : 0
% 0.19/0.56  # Termbank termtop insertions          : 132977
% 0.19/0.56  
% 0.19/0.56  # -------------------------------------------------
% 0.19/0.56  # User time                : 0.211 s
% 0.19/0.56  # System time              : 0.010 s
% 0.19/0.56  # Total time               : 0.222 s
% 0.19/0.56  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
