%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:08 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 560 expanded)
%              Number of clauses        :   45 ( 303 expanded)
%              Number of leaves         :    5 ( 127 expanded)
%              Depth                    :   16
%              Number of atoms          :  162 (2222 expanded)
%              Number of equality atoms :   72 ( 897 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t195_relat_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_hidden(X5,X7)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(k4_tarski(X13,esk1_3(X11,X12,X13)),X11)
        | X12 != k1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X11)
        | r2_hidden(X15,X12)
        | X12 != k1_relat_1(X11) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | ~ r2_hidden(k4_tarski(esk2_2(X17,X18),X20),X17)
        | X18 = k1_relat_1(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | r2_hidden(k4_tarski(esk2_2(X17,X18),esk3_2(X17,X18)),X17)
        | X18 = k1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),X1),X1) ),
    inference(ef,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk2_2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k4_tarski(esk4_3(X22,X23,X24),X24),X22)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X27,X26),X22)
        | r2_hidden(X26,X23)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(esk5_2(X28,X29),X29)
        | ~ r2_hidden(k4_tarski(X31,esk5_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) )
      & ( r2_hidden(esk5_2(X28,X29),X29)
        | r2_hidden(k4_tarski(esk6_2(X28,X29),esk5_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_23,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X1 = k1_relat_1(X2)
    | ~ r2_hidden(esk2_2(X2,X1),k1_relat_1(X2))
    | ~ r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk2_2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_32])).

cnf(c_0_35,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk2_2(k1_xboole_0,k2_relat_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_36,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_35]),c_0_32])]),c_0_34])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
              & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t195_relat_1])).

cnf(c_0_39,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,X1),X1)
    | r2_hidden(esk5_2(k1_xboole_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_37])).

cnf(c_0_41,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk5_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

fof(c_0_43,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & ( k1_relat_1(k2_zfmisc_1(esk7_0,esk8_0)) != esk7_0
      | k2_relat_1(k2_zfmisc_1(esk7_0,esk8_0)) != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_44,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_15]),c_0_15])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,X1),X1) ),
    inference(ef,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_14])).

cnf(c_0_47,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | r2_hidden(esk5_2(k2_zfmisc_1(X1,X2),X2),X2) ),
    inference(ef,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk7_0,esk8_0)) != esk7_0
    | k2_relat_1(k2_zfmisc_1(esk7_0,esk8_0)) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X2 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk7_0,esk8_0)) != esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_53,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 2.60/2.84  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 2.60/2.84  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.60/2.84  #
% 2.60/2.84  # Preprocessing time       : 0.027 s
% 2.60/2.84  # Presaturation interreduction done
% 2.60/2.84  
% 2.60/2.84  # Proof found!
% 2.60/2.84  # SZS status Theorem
% 2.60/2.84  # SZS output start CNFRefutation
% 2.60/2.84  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.60/2.84  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.60/2.84  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.60/2.84  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.60/2.84  fof(t195_relat_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 2.60/2.84  fof(c_0_5, plain, ![X5, X6, X7, X8]:(((r2_hidden(X5,X7)|~r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)))&(r2_hidden(X6,X8)|~r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8))))&(~r2_hidden(X5,X7)|~r2_hidden(X6,X8)|r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 2.60/2.84  fof(c_0_6, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:(((~r2_hidden(X13,X12)|r2_hidden(k4_tarski(X13,esk1_3(X11,X12,X13)),X11)|X12!=k1_relat_1(X11))&(~r2_hidden(k4_tarski(X15,X16),X11)|r2_hidden(X15,X12)|X12!=k1_relat_1(X11)))&((~r2_hidden(esk2_2(X17,X18),X18)|~r2_hidden(k4_tarski(esk2_2(X17,X18),X20),X17)|X18=k1_relat_1(X17))&(r2_hidden(esk2_2(X17,X18),X18)|r2_hidden(k4_tarski(esk2_2(X17,X18),esk3_2(X17,X18)),X17)|X18=k1_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 2.60/2.84  cnf(c_0_7, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 2.60/2.84  cnf(c_0_8, plain, (r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.60/2.84  fof(c_0_9, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 2.60/2.84  cnf(c_0_10, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.60/2.84  cnf(c_0_11, plain, (X1=k1_relat_1(k2_zfmisc_1(X2,X3))|r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X1)|r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X2)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 2.60/2.84  cnf(c_0_12, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.60/2.84  cnf(c_0_13, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_10])).
% 2.60/2.84  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 2.60/2.84  cnf(c_0_15, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),X1),X1)), inference(ef,[status(thm)],[c_0_11])).
% 2.60/2.84  cnf(c_0_16, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_12])).
% 2.60/2.84  cnf(c_0_17, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.60/2.84  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.60/2.84  cnf(c_0_19, plain, (r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X3)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 2.60/2.84  cnf(c_0_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(esk2_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 2.60/2.84  cnf(c_0_21, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 2.60/2.84  fof(c_0_22, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(esk4_3(X22,X23,X24),X24),X22)|X23!=k2_relat_1(X22))&(~r2_hidden(k4_tarski(X27,X26),X22)|r2_hidden(X26,X23)|X23!=k2_relat_1(X22)))&((~r2_hidden(esk5_2(X28,X29),X29)|~r2_hidden(k4_tarski(X31,esk5_2(X28,X29)),X28)|X29=k2_relat_1(X28))&(r2_hidden(esk5_2(X28,X29),X29)|r2_hidden(k4_tarski(esk6_2(X28,X29),esk5_2(X28,X29)),X28)|X29=k2_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 2.60/2.84  cnf(c_0_23, plain, (X2=k1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.60/2.84  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,esk1_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_18])).
% 2.60/2.84  cnf(c_0_25, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(X1,k1_relat_1(k1_xboole_0))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 2.60/2.84  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 2.60/2.84  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.60/2.84  cnf(c_0_28, plain, (X1=k1_relat_1(X2)|~r2_hidden(esk2_2(X2,X1),k1_relat_1(X2))|~r2_hidden(esk2_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.60/2.84  cnf(c_0_29, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(esk2_2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 2.60/2.84  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 2.60/2.84  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_27])).
% 2.60/2.84  cnf(c_0_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_20])).
% 2.60/2.84  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.60/2.84  cnf(c_0_34, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_21]), c_0_32])).
% 2.60/2.84  cnf(c_0_35, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(esk2_2(k1_xboole_0,k2_relat_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.60/2.84  cnf(c_0_36, plain, (r2_hidden(esk5_2(X1,X2),X2)|r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.60/2.84  cnf(c_0_37, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_35]), c_0_32])]), c_0_34])).
% 2.60/2.84  fof(c_0_38, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2))))), inference(assume_negation,[status(cth)],[t195_relat_1])).
% 2.60/2.84  cnf(c_0_39, plain, (X1=k1_relat_1(k2_zfmisc_1(X2,X3))|~r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X1)|~r2_hidden(esk2_2(k2_zfmisc_1(X2,X3),X1),X2)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_23, c_0_14])).
% 2.60/2.84  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,X1),X1)|r2_hidden(esk5_2(k1_xboole_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_37])).
% 2.60/2.84  cnf(c_0_41, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk5_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk5_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.60/2.84  cnf(c_0_42, plain, (X1=k2_relat_1(k2_zfmisc_1(X2,X3))|r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X1)|r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 2.60/2.84  fof(c_0_43, negated_conjecture, ((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&(k1_relat_1(k2_zfmisc_1(esk7_0,esk8_0))!=esk7_0|k2_relat_1(k2_zfmisc_1(esk7_0,esk8_0))!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 2.60/2.84  cnf(c_0_44, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_15]), c_0_15])).
% 2.60/2.84  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,X1),X1)), inference(ef,[status(thm)],[c_0_40])).
% 2.60/2.84  cnf(c_0_46, plain, (X1=k2_relat_1(k2_zfmisc_1(X2,X3))|~r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X1)|~r2_hidden(esk5_2(k2_zfmisc_1(X2,X3),X1),X3)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_41, c_0_14])).
% 2.60/2.84  cnf(c_0_47, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|r2_hidden(esk5_2(k2_zfmisc_1(X1,X2),X2),X2)), inference(ef,[status(thm)],[c_0_42])).
% 2.60/2.84  cnf(c_0_48, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk7_0,esk8_0))!=esk7_0|k2_relat_1(k2_zfmisc_1(esk7_0,esk8_0))!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.60/2.84  cnf(c_0_49, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X2=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 2.60/2.84  cnf(c_0_50, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.60/2.84  cnf(c_0_51, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_47])).
% 2.60/2.84  cnf(c_0_52, negated_conjecture, (k2_relat_1(k2_zfmisc_1(esk7_0,esk8_0))!=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 2.60/2.84  cnf(c_0_53, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_45])).
% 2.60/2.84  cnf(c_0_54, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.60/2.84  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 2.60/2.84  # SZS output end CNFRefutation
% 2.60/2.84  # Proof object total steps             : 56
% 2.60/2.84  # Proof object clause steps            : 45
% 2.60/2.84  # Proof object formula steps           : 11
% 2.60/2.84  # Proof object conjectures             : 8
% 2.60/2.84  # Proof object clause conjectures      : 5
% 2.60/2.84  # Proof object formula conjectures     : 3
% 2.60/2.84  # Proof object initial clauses used    : 15
% 2.60/2.84  # Proof object initial formulas used   : 5
% 2.60/2.84  # Proof object generating inferences   : 25
% 2.60/2.84  # Proof object simplifying inferences  : 16
% 2.60/2.84  # Training examples: 0 positive, 0 negative
% 2.60/2.84  # Parsed axioms                        : 5
% 2.60/2.84  # Removed by relevancy pruning/SinE    : 0
% 2.60/2.84  # Initial clauses                      : 17
% 2.60/2.84  # Removed in clause preprocessing      : 0
% 2.60/2.84  # Initial clauses in saturation        : 17
% 2.60/2.84  # Processed clauses                    : 5270
% 2.60/2.84  # ...of these trivial                  : 5
% 2.60/2.84  # ...subsumed                          : 3966
% 2.60/2.84  # ...remaining for further processing  : 1299
% 2.60/2.84  # Other redundant clauses eliminated   : 18698
% 2.60/2.84  # Clauses deleted for lack of memory   : 0
% 2.60/2.84  # Backward-subsumed                    : 13
% 2.60/2.84  # Backward-rewritten                   : 17
% 2.60/2.84  # Generated clauses                    : 518964
% 2.60/2.84  # ...of the previous two non-trivial   : 408331
% 2.60/2.84  # Contextual simplify-reflections      : 10
% 2.60/2.84  # Paramodulations                      : 500172
% 2.60/2.84  # Factorizations                       : 94
% 2.60/2.84  # Equation resolutions                 : 18698
% 2.60/2.84  # Propositional unsat checks           : 0
% 2.60/2.84  #    Propositional check models        : 0
% 2.60/2.84  #    Propositional check unsatisfiable : 0
% 2.60/2.84  #    Propositional clauses             : 0
% 2.60/2.84  #    Propositional clauses after purity: 0
% 2.60/2.84  #    Propositional unsat core size     : 0
% 2.60/2.84  #    Propositional preprocessing time  : 0.000
% 2.60/2.84  #    Propositional encoding time       : 0.000
% 2.60/2.84  #    Propositional solver time         : 0.000
% 2.60/2.84  #    Success case prop preproc time    : 0.000
% 2.60/2.84  #    Success case prop encoding time   : 0.000
% 2.60/2.84  #    Success case prop solver time     : 0.000
% 2.60/2.84  # Current number of processed clauses  : 1246
% 2.60/2.84  #    Positive orientable unit clauses  : 5
% 2.60/2.84  #    Positive unorientable unit clauses: 0
% 2.60/2.84  #    Negative unit clauses             : 3
% 2.60/2.84  #    Non-unit-clauses                  : 1238
% 2.60/2.84  # Current number of unprocessed clauses: 402430
% 2.60/2.84  # ...number of literals in the above   : 1476284
% 2.60/2.84  # Current number of archived formulas  : 0
% 2.60/2.84  # Current number of archived clauses   : 47
% 2.60/2.84  # Clause-clause subsumption calls (NU) : 587921
% 2.60/2.84  # Rec. Clause-clause subsumption calls : 257632
% 2.60/2.84  # Non-unit clause-clause subsumptions  : 3978
% 2.60/2.84  # Unit Clause-clause subsumption calls : 276
% 2.60/2.84  # Rewrite failures with RHS unbound    : 0
% 2.60/2.84  # BW rewrite match attempts            : 33
% 2.60/2.84  # BW rewrite match successes           : 2
% 2.60/2.84  # Condensation attempts                : 0
% 2.60/2.84  # Condensation successes               : 0
% 2.60/2.84  # Termbank termtop insertions          : 9084217
% 2.71/2.86  
% 2.71/2.86  # -------------------------------------------------
% 2.71/2.86  # User time                : 2.385 s
% 2.71/2.86  # System time              : 0.137 s
% 2.71/2.86  # Total time               : 2.522 s
% 2.71/2.86  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
