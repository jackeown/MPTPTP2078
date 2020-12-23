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
% DateTime   : Thu Dec  3 10:44:47 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 513 expanded)
%              Number of clauses        :   42 ( 217 expanded)
%              Number of leaves         :    8 ( 138 expanded)
%              Depth                    :   10
%              Number of atoms          :  152 (1293 expanded)
%              Number of equality atoms :   48 ( 636 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tarski(k1_tarski(X27),X28)
        | r2_hidden(X27,X28) )
      & ( ~ r2_hidden(X27,X28)
        | r1_tarski(k1_tarski(X27),X28) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_17,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & k3_xboole_0(esk3_0,esk4_0) = k1_tarski(esk5_0)
    & r2_hidden(esk5_0,esk2_0)
    & k3_xboole_0(esk2_0,esk4_0) != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X4)
    | X4 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_25]),c_0_26]),c_0_27]),c_0_11])).

cnf(c_0_36,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_27]),c_0_11])).

cnf(c_0_38,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_11])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X3))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)))
    | r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(esk5_0,X2)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X3,k4_xboole_0(X3,X4))
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_44,c_0_11])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_48])]),c_0_37]),c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_53])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X3,k4_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_35]),c_0_37]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.56/1.75  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.56/1.75  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.56/1.75  #
% 1.56/1.75  # Preprocessing time       : 0.027 s
% 1.56/1.75  # Presaturation interreduction done
% 1.56/1.75  
% 1.56/1.75  # Proof found!
% 1.56/1.75  # SZS status Theorem
% 1.56/1.75  # SZS output start CNFRefutation
% 1.56/1.75  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.56/1.75  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.56/1.75  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.56/1.75  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 1.56/1.75  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.56/1.75  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.56/1.75  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.56/1.75  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.56/1.75  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.56/1.75  fof(c_0_9, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.56/1.75  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.56/1.75  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.56/1.75  fof(c_0_12, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.56/1.75  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 1.56/1.75  cnf(c_0_14, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 1.56/1.75  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.56/1.75  fof(c_0_16, plain, ![X27, X28]:((~r1_tarski(k1_tarski(X27),X28)|r2_hidden(X27,X28))&(~r2_hidden(X27,X28)|r1_tarski(k1_tarski(X27),X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 1.56/1.75  fof(c_0_17, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.56/1.75  fof(c_0_18, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.56/1.75  fof(c_0_19, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.56/1.75  cnf(c_0_20, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.56/1.75  fof(c_0_21, negated_conjecture, (((r1_tarski(esk2_0,esk3_0)&k3_xboole_0(esk3_0,esk4_0)=k1_tarski(esk5_0))&r2_hidden(esk5_0,esk2_0))&k3_xboole_0(esk2_0,esk4_0)!=k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 1.56/1.75  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_14])).
% 1.56/1.75  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_11])).
% 1.56/1.75  cnf(c_0_24, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.56/1.75  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.56/1.75  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.56/1.75  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.56/1.75  cnf(c_0_28, plain, (r2_hidden(X1,X4)|X4!=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_11])).
% 1.56/1.75  cnf(c_0_29, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.56/1.75  cnf(c_0_30, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.56/1.75  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.56/1.75  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.56/1.75  cnf(c_0_33, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 1.56/1.75  cnf(c_0_34, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_28])).
% 1.56/1.75  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_25]), c_0_26]), c_0_27]), c_0_11])).
% 1.56/1.75  cnf(c_0_36, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.56/1.75  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_26]), c_0_27]), c_0_11])).
% 1.56/1.75  cnf(c_0_38, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_31, c_0_11])).
% 1.56/1.75  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X3))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.56/1.75  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.56/1.75  cnf(c_0_41, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_36, c_0_11])).
% 1.56/1.75  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)))|r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.56/1.75  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.56/1.75  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.56/1.75  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(esk5_0,X2)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.56/1.75  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.56/1.75  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X3,k4_xboole_0(X3,X4))|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X4)|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 1.56/1.75  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_22])).
% 1.56/1.75  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_43])).
% 1.56/1.75  cnf(c_0_50, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_44, c_0_11])).
% 1.56/1.75  cnf(c_0_51, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.56/1.75  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.56/1.75  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_48])]), c_0_37]), c_0_49])).
% 1.56/1.75  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_50])).
% 1.56/1.75  cnf(c_0_55, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_51, c_0_11])).
% 1.56/1.75  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_53])).
% 1.56/1.75  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X3,k4_xboole_0(X3,X4))|r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)|r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.56/1.75  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_35]), c_0_37]), c_0_53]), ['proof']).
% 1.56/1.75  # SZS output end CNFRefutation
% 1.56/1.75  # Proof object total steps             : 59
% 1.56/1.75  # Proof object clause steps            : 42
% 1.56/1.75  # Proof object formula steps           : 17
% 1.56/1.75  # Proof object conjectures             : 18
% 1.56/1.75  # Proof object clause conjectures      : 15
% 1.56/1.75  # Proof object formula conjectures     : 3
% 1.56/1.75  # Proof object initial clauses used    : 16
% 1.56/1.75  # Proof object initial formulas used   : 8
% 1.56/1.75  # Proof object generating inferences   : 13
% 1.56/1.75  # Proof object simplifying inferences  : 31
% 1.56/1.75  # Training examples: 0 positive, 0 negative
% 1.56/1.75  # Parsed axioms                        : 9
% 1.56/1.75  # Removed by relevancy pruning/SinE    : 0
% 1.56/1.75  # Initial clauses                      : 18
% 1.56/1.75  # Removed in clause preprocessing      : 4
% 1.56/1.75  # Initial clauses in saturation        : 14
% 1.56/1.75  # Processed clauses                    : 1647
% 1.56/1.75  # ...of these trivial                  : 4
% 1.56/1.75  # ...subsumed                          : 769
% 1.56/1.75  # ...remaining for further processing  : 874
% 1.56/1.75  # Other redundant clauses eliminated   : 363
% 1.56/1.75  # Clauses deleted for lack of memory   : 0
% 1.56/1.75  # Backward-subsumed                    : 75
% 1.56/1.75  # Backward-rewritten                   : 8
% 1.56/1.75  # Generated clauses                    : 79438
% 1.56/1.75  # ...of the previous two non-trivial   : 78452
% 1.56/1.75  # Contextual simplify-reflections      : 33
% 1.56/1.75  # Paramodulations                      : 78903
% 1.56/1.75  # Factorizations                       : 172
% 1.56/1.75  # Equation resolutions                 : 363
% 1.56/1.75  # Propositional unsat checks           : 0
% 1.56/1.75  #    Propositional check models        : 0
% 1.56/1.75  #    Propositional check unsatisfiable : 0
% 1.56/1.75  #    Propositional clauses             : 0
% 1.56/1.75  #    Propositional clauses after purity: 0
% 1.56/1.75  #    Propositional unsat core size     : 0
% 1.56/1.75  #    Propositional preprocessing time  : 0.000
% 1.56/1.75  #    Propositional encoding time       : 0.000
% 1.56/1.75  #    Propositional solver time         : 0.000
% 1.56/1.75  #    Success case prop preproc time    : 0.000
% 1.56/1.75  #    Success case prop encoding time   : 0.000
% 1.56/1.75  #    Success case prop solver time     : 0.000
% 1.56/1.75  # Current number of processed clauses  : 774
% 1.56/1.75  #    Positive orientable unit clauses  : 11
% 1.56/1.75  #    Positive unorientable unit clauses: 0
% 1.56/1.75  #    Negative unit clauses             : 3
% 1.56/1.75  #    Non-unit-clauses                  : 760
% 1.56/1.75  # Current number of unprocessed clauses: 76523
% 1.56/1.75  # ...number of literals in the above   : 466233
% 1.56/1.75  # Current number of archived formulas  : 0
% 1.56/1.75  # Current number of archived clauses   : 101
% 1.56/1.75  # Clause-clause subsumption calls (NU) : 49418
% 1.56/1.75  # Rec. Clause-clause subsumption calls : 10055
% 1.56/1.75  # Non-unit clause-clause subsumptions  : 876
% 1.56/1.75  # Unit Clause-clause subsumption calls : 412
% 1.56/1.75  # Rewrite failures with RHS unbound    : 0
% 1.56/1.75  # BW rewrite match attempts            : 19
% 1.56/1.75  # BW rewrite match successes           : 3
% 1.56/1.75  # Condensation attempts                : 0
% 1.56/1.75  # Condensation successes               : 0
% 1.56/1.75  # Termbank termtop insertions          : 2502217
% 1.56/1.75  
% 1.56/1.75  # -------------------------------------------------
% 1.56/1.75  # User time                : 1.357 s
% 1.56/1.75  # System time              : 0.040 s
% 1.56/1.75  # Total time               : 1.398 s
% 1.56/1.75  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
