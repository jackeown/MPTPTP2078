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
% DateTime   : Thu Dec  3 10:43:23 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 150 expanded)
%              Number of clauses        :   35 (  75 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 534 expanded)
%              Number of equality atoms :   31 ( 143 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t103_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
          & ! [X6,X7] :
              ~ ( X1 = k4_tarski(X6,X7)
                & r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    inference(assume_negation,[status(cth)],[t104_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,negated_conjecture,(
    ! [X36,X37] :
      ( r2_hidden(esk4_0,k3_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0)))
      & ( esk4_0 != k4_tarski(X36,X37)
        | ~ r2_hidden(X36,k3_xboole_0(esk5_0,esk7_0))
        | ~ r2_hidden(X37,k3_xboole_0(esk6_0,esk8_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( esk4_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(esk5_0,esk7_0))
    | ~ r2_hidden(X2,k3_xboole_0(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | X4 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X2,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk8_0)))
    | ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_11]),c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X21,X22,X23,X24] :
      ( ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,X24)) )
      & ( r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,X24)) )
      & ( ~ r2_hidden(X21,X23)
        | ~ r2_hidden(X22,X24)
        | r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X28] :
      ( ( r2_hidden(esk2_4(X25,X26,X27,X28),X26)
        | ~ r1_tarski(X25,k2_zfmisc_1(X26,X27))
        | ~ r2_hidden(X28,X25) )
      & ( r2_hidden(esk3_4(X25,X26,X27,X28),X27)
        | ~ r1_tarski(X25,k2_zfmisc_1(X26,X27))
        | ~ r2_hidden(X28,X25) )
      & ( X28 = k4_tarski(esk2_4(X25,X26,X27,X28),esk3_4(X25,X26,X27,X28))
        | ~ r1_tarski(X25,k2_zfmisc_1(X26,X27))
        | ~ r2_hidden(X28,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(X1,X2) != esk4_0
    | ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k4_tarski(X1,X2) != esk4_0
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X5)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,k2_zfmisc_1(X6,X5))
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0)))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X5)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,k2_zfmisc_1(X5,X6))
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk3_4(X1,X2,X3,esk4_0),esk8_0)
    | ~ r2_hidden(esk3_4(X1,X2,X3,esk4_0),esk6_0)
    | ~ r2_hidden(esk2_4(X1,X2,X3,esk4_0),esk7_0)
    | ~ r2_hidden(esk2_4(X1,X2,X3,esk4_0),esk5_0)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_4(k2_zfmisc_1(X1,X2),X1,X2,X3),X4)
    | ~ r2_hidden(X3,k2_zfmisc_1(X5,X4))
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_4(k2_zfmisc_1(X1,X2),X1,X2,X3),X4)
    | ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,esk8_0))
    | ~ r2_hidden(esk3_4(X1,X2,esk8_0,esk4_0),esk6_0)
    | ~ r2_hidden(esk2_4(X1,X2,esk8_0,esk4_0),esk7_0)
    | ~ r2_hidden(esk2_4(X1,X2,esk8_0,esk4_0),esk5_0)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_4(k2_zfmisc_1(X1,X2),X1,X2,esk4_0),esk6_0)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_4(k2_zfmisc_1(X1,X2),X1,X2,esk4_0),esk5_0)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_4(k2_zfmisc_1(X1,X2),X1,X2,esk4_0),esk7_0)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k2_zfmisc_1(X1,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_31])]),c_0_44]),c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_41,c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.36/3.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 3.36/3.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 3.36/3.54  #
% 3.36/3.54  # Preprocessing time       : 0.022 s
% 3.36/3.54  # Presaturation interreduction done
% 3.36/3.54  
% 3.36/3.54  # Proof found!
% 3.36/3.54  # SZS status Theorem
% 3.36/3.54  # SZS output start CNFRefutation
% 3.36/3.54  fof(t104_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))&![X6, X7]:~(((X1=k4_tarski(X6,X7)&r2_hidden(X6,k3_xboole_0(X2,X4)))&r2_hidden(X7,k3_xboole_0(X3,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_zfmisc_1)).
% 3.36/3.54  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.36/3.54  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.36/3.54  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.36/3.54  fof(t103_zfmisc_1, axiom, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 3.36/3.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/3.54  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))&![X6, X7]:~(((X1=k4_tarski(X6,X7)&r2_hidden(X6,k3_xboole_0(X2,X4)))&r2_hidden(X7,k3_xboole_0(X3,X5))))))), inference(assume_negation,[status(cth)],[t104_zfmisc_1])).
% 3.36/3.54  fof(c_0_7, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 3.36/3.54  fof(c_0_8, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 3.36/3.54  fof(c_0_9, negated_conjecture, ![X36, X37]:(r2_hidden(esk4_0,k3_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0)))&(esk4_0!=k4_tarski(X36,X37)|~r2_hidden(X36,k3_xboole_0(esk5_0,esk7_0))|~r2_hidden(X37,k3_xboole_0(esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 3.36/3.54  cnf(c_0_10, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 3.36/3.54  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.36/3.54  cnf(c_0_12, negated_conjecture, (esk4_0!=k4_tarski(X1,X2)|~r2_hidden(X1,k3_xboole_0(esk5_0,esk7_0))|~r2_hidden(X2,k3_xboole_0(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.36/3.54  cnf(c_0_13, plain, (r2_hidden(X1,X4)|X4!=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 3.36/3.54  cnf(c_0_14, negated_conjecture, (esk4_0!=k4_tarski(X1,X2)|~r2_hidden(X2,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk8_0)))|~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_11]), c_0_11])).
% 3.36/3.54  cnf(c_0_15, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_13])).
% 3.36/3.54  fof(c_0_16, plain, ![X21, X22, X23, X24]:(((r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,X24)))&(r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,X24))))&(~r2_hidden(X21,X23)|~r2_hidden(X22,X24)|r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 3.36/3.54  fof(c_0_17, plain, ![X25, X26, X27, X28]:(((r2_hidden(esk2_4(X25,X26,X27,X28),X26)|(~r1_tarski(X25,k2_zfmisc_1(X26,X27))|~r2_hidden(X28,X25)))&(r2_hidden(esk3_4(X25,X26,X27,X28),X27)|(~r1_tarski(X25,k2_zfmisc_1(X26,X27))|~r2_hidden(X28,X25))))&(X28=k4_tarski(esk2_4(X25,X26,X27,X28),esk3_4(X25,X26,X27,X28))|(~r1_tarski(X25,k2_zfmisc_1(X26,X27))|~r2_hidden(X28,X25)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).
% 3.36/3.54  fof(c_0_18, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.36/3.54  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 3.36/3.54  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 3.36/3.54  cnf(c_0_21, negated_conjecture, (k4_tarski(X1,X2)!=esk4_0|~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))|~r2_hidden(X2,esk8_0)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 3.36/3.54  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.36/3.54  cnf(c_0_23, plain, (X1=k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|~r1_tarski(X2,k2_zfmisc_1(X3,X4))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.36/3.54  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.36/3.54  cnf(c_0_25, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_19, c_0_11])).
% 3.36/3.54  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.36/3.54  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.36/3.54  cnf(c_0_28, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_20, c_0_11])).
% 3.36/3.54  cnf(c_0_29, negated_conjecture, (k4_tarski(X1,X2)!=esk4_0|~r2_hidden(X2,esk8_0)|~r2_hidden(X2,esk6_0)|~r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_15])).
% 3.36/3.54  cnf(c_0_30, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X5)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X4,k2_zfmisc_1(X6,X5))|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 3.36/3.54  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 3.36/3.54  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_25])).
% 3.36/3.54  cnf(c_0_33, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0))))), inference(rw,[status(thm)],[c_0_26, c_0_11])).
% 3.36/3.54  cnf(c_0_34, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X5)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X4,k2_zfmisc_1(X5,X6))|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 3.36/3.54  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_28])).
% 3.36/3.54  cnf(c_0_36, negated_conjecture, (~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(esk3_4(X1,X2,X3,esk4_0),esk8_0)|~r2_hidden(esk3_4(X1,X2,X3,esk4_0),esk6_0)|~r2_hidden(esk2_4(X1,X2,X3,esk4_0),esk7_0)|~r2_hidden(esk2_4(X1,X2,X3,esk4_0),esk5_0)|~r2_hidden(esk4_0,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23])])).
% 3.36/3.54  cnf(c_0_37, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.36/3.54  cnf(c_0_38, plain, (r2_hidden(esk3_4(k2_zfmisc_1(X1,X2),X1,X2,X3),X4)|~r2_hidden(X3,k2_zfmisc_1(X5,X4))|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 3.36/3.54  cnf(c_0_39, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.36/3.54  cnf(c_0_40, plain, (r2_hidden(esk2_4(k2_zfmisc_1(X1,X2),X1,X2,X3),X4)|~r2_hidden(X3,k2_zfmisc_1(X4,X5))|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 3.36/3.54  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 3.36/3.54  cnf(c_0_42, negated_conjecture, (~r1_tarski(X1,k2_zfmisc_1(X2,esk8_0))|~r2_hidden(esk3_4(X1,X2,esk8_0,esk4_0),esk6_0)|~r2_hidden(esk2_4(X1,X2,esk8_0,esk4_0),esk7_0)|~r2_hidden(esk2_4(X1,X2,esk8_0,esk4_0),esk5_0)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 3.36/3.54  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_4(k2_zfmisc_1(X1,X2),X1,X2,esk4_0),esk6_0)|~r2_hidden(esk4_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 3.36/3.54  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_4(k2_zfmisc_1(X1,X2),X1,X2,esk4_0),esk5_0)|~r2_hidden(esk4_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 3.36/3.54  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_4(k2_zfmisc_1(X1,X2),X1,X2,esk4_0),esk7_0)|~r2_hidden(esk4_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.36/3.54  cnf(c_0_46, negated_conjecture, (~r2_hidden(esk4_0,k2_zfmisc_1(X1,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_31])]), c_0_44]), c_0_45])).
% 3.36/3.54  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_41, c_0_46]), ['proof']).
% 3.36/3.54  # SZS output end CNFRefutation
% 3.36/3.54  # Proof object total steps             : 48
% 3.36/3.54  # Proof object clause steps            : 35
% 3.36/3.54  # Proof object formula steps           : 13
% 3.36/3.54  # Proof object conjectures             : 18
% 3.36/3.54  # Proof object clause conjectures      : 15
% 3.36/3.54  # Proof object formula conjectures     : 3
% 3.36/3.54  # Proof object initial clauses used    : 11
% 3.36/3.54  # Proof object initial formulas used   : 6
% 3.36/3.54  # Proof object generating inferences   : 14
% 3.36/3.54  # Proof object simplifying inferences  : 16
% 3.36/3.54  # Training examples: 0 positive, 0 negative
% 3.36/3.54  # Parsed axioms                        : 6
% 3.36/3.54  # Removed by relevancy pruning/SinE    : 0
% 3.36/3.54  # Initial clauses                      : 18
% 3.36/3.54  # Removed in clause preprocessing      : 1
% 3.36/3.54  # Initial clauses in saturation        : 17
% 3.36/3.54  # Processed clauses                    : 4332
% 3.36/3.54  # ...of these trivial                  : 65
% 3.36/3.54  # ...subsumed                          : 2556
% 3.36/3.54  # ...remaining for further processing  : 1711
% 3.36/3.54  # Other redundant clauses eliminated   : 1226
% 3.36/3.54  # Clauses deleted for lack of memory   : 0
% 3.36/3.54  # Backward-subsumed                    : 121
% 3.36/3.54  # Backward-rewritten                   : 70
% 3.36/3.54  # Generated clauses                    : 275343
% 3.36/3.54  # ...of the previous two non-trivial   : 271675
% 3.36/3.54  # Contextual simplify-reflections      : 38
% 3.36/3.54  # Paramodulations                      : 273841
% 3.36/3.54  # Factorizations                       : 266
% 3.36/3.54  # Equation resolutions                 : 1226
% 3.36/3.54  # Propositional unsat checks           : 0
% 3.36/3.54  #    Propositional check models        : 0
% 3.36/3.54  #    Propositional check unsatisfiable : 0
% 3.36/3.54  #    Propositional clauses             : 0
% 3.36/3.54  #    Propositional clauses after purity: 0
% 3.36/3.54  #    Propositional unsat core size     : 0
% 3.36/3.54  #    Propositional preprocessing time  : 0.000
% 3.36/3.54  #    Propositional encoding time       : 0.000
% 3.36/3.54  #    Propositional solver time         : 0.000
% 3.36/3.54  #    Success case prop preproc time    : 0.000
% 3.36/3.54  #    Success case prop encoding time   : 0.000
% 3.36/3.54  #    Success case prop solver time     : 0.000
% 3.36/3.54  # Current number of processed clauses  : 1489
% 3.36/3.54  #    Positive orientable unit clauses  : 123
% 3.36/3.54  #    Positive unorientable unit clauses: 0
% 3.36/3.54  #    Negative unit clauses             : 6
% 3.36/3.54  #    Non-unit-clauses                  : 1360
% 3.36/3.54  # Current number of unprocessed clauses: 266983
% 3.36/3.54  # ...number of literals in the above   : 1427080
% 3.36/3.54  # Current number of archived formulas  : 0
% 3.36/3.54  # Current number of archived clauses   : 218
% 3.36/3.54  # Clause-clause subsumption calls (NU) : 183831
% 3.36/3.54  # Rec. Clause-clause subsumption calls : 104806
% 3.36/3.54  # Non-unit clause-clause subsumptions  : 2679
% 3.36/3.54  # Unit Clause-clause subsumption calls : 2355
% 3.36/3.54  # Rewrite failures with RHS unbound    : 0
% 3.36/3.54  # BW rewrite match attempts            : 1270
% 3.36/3.54  # BW rewrite match successes           : 43
% 3.36/3.54  # Condensation attempts                : 0
% 3.36/3.54  # Condensation successes               : 0
% 3.36/3.54  # Termbank termtop insertions          : 7685959
% 3.36/3.55  
% 3.36/3.55  # -------------------------------------------------
% 3.36/3.55  # User time                : 3.089 s
% 3.36/3.55  # System time              : 0.120 s
% 3.36/3.55  # Total time               : 3.210 s
% 3.36/3.55  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
