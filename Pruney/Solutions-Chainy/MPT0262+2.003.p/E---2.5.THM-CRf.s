%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:55 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  52 expanded)
%              Number of clauses        :   19 (  25 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  109 ( 205 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t57_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X20
        | X23 = X21
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( esk3_3(X25,X26,X27) != X25
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( esk3_3(X25,X26,X27) != X26
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X27)
        | esk3_3(X25,X26,X27) = X25
        | esk3_3(X25,X26,X27) = X26
        | X27 = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X3,X2)
          & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t57_zfmisc_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0)
    & ~ r2_hidden(esk6_0,esk5_0)
    & ~ r1_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_22,plain,
    ( esk2_2(k1_enumset1(X1,X1,X2),X3) = X2
    | esk2_2(k1_enumset1(X1,X1,X2),X3) = X1
    | r1_xboole_0(k1_enumset1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( esk2_2(k1_enumset1(X1,X1,X2),X3) = X2
    | r1_xboole_0(k1_enumset1(X1,X1,X2),X3)
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_xboole_0(k1_enumset1(esk4_0,esk4_0,esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_9])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k1_enumset1(X1,X1,X2),X3)
    | r2_hidden(X1,X3)
    | r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:36:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.43  #
% 0.18/0.43  # Preprocessing time       : 0.015 s
% 0.18/0.43  # Presaturation interreduction done
% 0.18/0.43  
% 0.18/0.43  # Proof found!
% 0.18/0.43  # SZS status Theorem
% 0.18/0.43  # SZS output start CNFRefutation
% 0.18/0.43  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.43  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.18/0.43  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.18/0.43  fof(t57_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.18/0.43  fof(c_0_5, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X23,X22)|(X23=X20|X23=X21)|X22!=k2_tarski(X20,X21))&((X24!=X20|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))))&(((esk3_3(X25,X26,X27)!=X25|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26))&(esk3_3(X25,X26,X27)!=X26|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26)))&(r2_hidden(esk3_3(X25,X26,X27),X27)|(esk3_3(X25,X26,X27)=X25|esk3_3(X25,X26,X27)=X26)|X27=k2_tarski(X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.43  fof(c_0_6, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.43  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.18/0.43  cnf(c_0_8, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.43  cnf(c_0_9, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.43  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.43  fof(c_0_11, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.18/0.43  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.43  cnf(c_0_13, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.18/0.43  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_10])).
% 0.18/0.43  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.43  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2))))), inference(assume_negation,[status(cth)],[t57_zfmisc_1])).
% 0.18/0.43  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.18/0.43  cnf(c_0_18, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.18/0.43  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.43  fof(c_0_20, negated_conjecture, ((~r2_hidden(esk4_0,esk5_0)&~r2_hidden(esk6_0,esk5_0))&~r1_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.18/0.43  cnf(c_0_21, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.18/0.43  cnf(c_0_22, plain, (esk2_2(k1_enumset1(X1,X1,X2),X3)=X2|esk2_2(k1_enumset1(X1,X1,X2),X3)=X1|r1_xboole_0(k1_enumset1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.43  cnf(c_0_23, negated_conjecture, (~r1_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.43  cnf(c_0_24, plain, (esk2_2(k1_enumset1(X1,X1,X2),X3)=X2|r1_xboole_0(k1_enumset1(X1,X1,X2),X3)|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.43  cnf(c_0_25, negated_conjecture, (~r1_xboole_0(k1_enumset1(esk4_0,esk4_0,esk6_0),esk5_0)), inference(rw,[status(thm)],[c_0_23, c_0_9])).
% 0.18/0.43  cnf(c_0_26, plain, (r1_xboole_0(k1_enumset1(X1,X1,X2),X3)|r2_hidden(X1,X3)|r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_21, c_0_24])).
% 0.18/0.43  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.43  cnf(c_0_28, negated_conjecture, (~r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.43  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), ['proof']).
% 0.18/0.43  # SZS output end CNFRefutation
% 0.18/0.43  # Proof object total steps             : 30
% 0.18/0.43  # Proof object clause steps            : 19
% 0.18/0.43  # Proof object formula steps           : 11
% 0.18/0.43  # Proof object conjectures             : 8
% 0.18/0.43  # Proof object clause conjectures      : 5
% 0.18/0.43  # Proof object formula conjectures     : 3
% 0.18/0.43  # Proof object initial clauses used    : 8
% 0.18/0.43  # Proof object initial formulas used   : 5
% 0.18/0.43  # Proof object generating inferences   : 6
% 0.18/0.43  # Proof object simplifying inferences  : 7
% 0.18/0.43  # Training examples: 0 positive, 0 negative
% 0.18/0.43  # Parsed axioms                        : 5
% 0.18/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.43  # Initial clauses                      : 18
% 0.18/0.43  # Removed in clause preprocessing      : 1
% 0.18/0.43  # Initial clauses in saturation        : 17
% 0.18/0.43  # Processed clauses                    : 580
% 0.18/0.43  # ...of these trivial                  : 0
% 0.18/0.43  # ...subsumed                          : 369
% 0.18/0.43  # ...remaining for further processing  : 211
% 0.18/0.43  # Other redundant clauses eliminated   : 56
% 0.18/0.43  # Clauses deleted for lack of memory   : 0
% 0.18/0.43  # Backward-subsumed                    : 0
% 0.18/0.43  # Backward-rewritten                   : 0
% 0.18/0.43  # Generated clauses                    : 5685
% 0.18/0.43  # ...of the previous two non-trivial   : 5356
% 0.18/0.43  # Contextual simplify-reflections      : 4
% 0.18/0.43  # Paramodulations                      : 5581
% 0.18/0.43  # Factorizations                       : 50
% 0.18/0.43  # Equation resolutions                 : 56
% 0.18/0.43  # Propositional unsat checks           : 0
% 0.18/0.43  #    Propositional check models        : 0
% 0.18/0.43  #    Propositional check unsatisfiable : 0
% 0.18/0.43  #    Propositional clauses             : 0
% 0.18/0.43  #    Propositional clauses after purity: 0
% 0.18/0.43  #    Propositional unsat core size     : 0
% 0.18/0.43  #    Propositional preprocessing time  : 0.000
% 0.18/0.43  #    Propositional encoding time       : 0.000
% 0.18/0.43  #    Propositional solver time         : 0.000
% 0.18/0.43  #    Success case prop preproc time    : 0.000
% 0.18/0.43  #    Success case prop encoding time   : 0.000
% 0.18/0.43  #    Success case prop solver time     : 0.000
% 0.18/0.43  # Current number of processed clauses  : 188
% 0.18/0.43  #    Positive orientable unit clauses  : 3
% 0.18/0.43  #    Positive unorientable unit clauses: 0
% 0.18/0.43  #    Negative unit clauses             : 3
% 0.18/0.43  #    Non-unit-clauses                  : 182
% 0.18/0.43  # Current number of unprocessed clauses: 4792
% 0.18/0.43  # ...number of literals in the above   : 27989
% 0.18/0.43  # Current number of archived formulas  : 0
% 0.18/0.43  # Current number of archived clauses   : 18
% 0.18/0.43  # Clause-clause subsumption calls (NU) : 8835
% 0.18/0.43  # Rec. Clause-clause subsumption calls : 7623
% 0.18/0.43  # Non-unit clause-clause subsumptions  : 373
% 0.18/0.43  # Unit Clause-clause subsumption calls : 9
% 0.18/0.43  # Rewrite failures with RHS unbound    : 0
% 0.18/0.43  # BW rewrite match attempts            : 5
% 0.18/0.43  # BW rewrite match successes           : 0
% 0.18/0.43  # Condensation attempts                : 0
% 0.18/0.43  # Condensation successes               : 0
% 0.18/0.43  # Termbank termtop insertions          : 95943
% 0.18/0.43  
% 0.18/0.43  # -------------------------------------------------
% 0.18/0.43  # User time                : 0.095 s
% 0.18/0.43  # System time              : 0.003 s
% 0.18/0.43  # Total time               : 0.098 s
% 0.18/0.43  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
