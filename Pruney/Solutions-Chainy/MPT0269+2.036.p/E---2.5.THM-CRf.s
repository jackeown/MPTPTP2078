%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 328 expanded)
%              Number of clauses        :   46 ( 170 expanded)
%              Number of leaves         :    5 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 (1137 expanded)
%              Number of equality atoms :   77 ( 578 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t66_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
        & X1 != k1_xboole_0
        & X1 != k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X22,X23] :
      ( ( k4_xboole_0(k1_tarski(X22),X23) != k1_xboole_0
        | r2_hidden(X22,X23) )
      & ( ~ r2_hidden(X22,X23)
        | k4_xboole_0(k1_tarski(X22),X23) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
          & X1 != k1_xboole_0
          & X1 != k1_tarski(X2) ) ),
    inference(assume_negation,[status(cth)],[t66_zfmisc_1])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) = k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk3_0 != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_tarski(esk4_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_tarski(X3,X3))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k2_tarski(X2,X2))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_8])).

cnf(c_0_30,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_23])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_25])).

cnf(c_0_32,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_35,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k2_tarski(esk4_0,esk4_0))
    | X2 != k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 != k2_tarski(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_8])).

cnf(c_0_39,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk2_2(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_8])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k2_tarski(esk4_0,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( esk2_2(esk4_0,X1) = esk4_0
    | r2_hidden(esk2_2(esk4_0,X1),X1)
    | X1 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,esk3_0),k2_tarski(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_50,negated_conjecture,
    ( esk2_2(esk4_0,esk3_0) = esk4_0
    | r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk1_3(X1,X1,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_8])).

cnf(c_0_54,negated_conjecture,
    ( esk2_2(esk4_0,esk3_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_50]),c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:38:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.13/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.38  fof(t66_zfmisc_1, conjecture, ![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 0.13/0.38  fof(c_0_5, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  cnf(c_0_7, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_8, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_9, plain, ![X22, X23]:((k4_xboole_0(k1_tarski(X22),X23)!=k1_xboole_0|r2_hidden(X22,X23))&(~r2_hidden(X22,X23)|k4_xboole_0(k1_tarski(X22),X23)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_10, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.38  cnf(c_0_11, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_hidden(X1,X2)|X2!=k2_tarski(X1,X1)), inference(er,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_13, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t66_zfmisc_1])).
% 0.13/0.38  cnf(c_0_15, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_8])).
% 0.13/0.38  cnf(c_0_16, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ((k4_xboole_0(esk3_0,k1_tarski(esk4_0))=k1_xboole_0&esk3_0!=k1_xboole_0)&esk3_0!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.38  cnf(c_0_19, plain, (k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (k4_xboole_0(esk3_0,k1_tarski(esk4_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_23, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_tarski(X3,X3))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, plain, (~r2_hidden(X1,k2_tarski(X2,X2))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_28, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_8])).
% 0.13/0.38  cnf(c_0_30, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_19]), c_0_23])).
% 0.13/0.38  cnf(c_0_31, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_25])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk3_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_34, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_35, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,k2_tarski(esk4_0,esk4_0))|X2!=k1_xboole_0|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.13/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (esk3_0!=k2_tarski(esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_33, c_0_8])).
% 0.13/0.38  cnf(c_0_39, plain, (X2=k2_tarski(X1,X1)|esk2_2(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_34, c_0_8])).
% 0.13/0.38  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_41, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_8])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,k2_tarski(esk4_0,esk4_0))|~r2_hidden(X1,esk3_0)), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[c_0_32, c_0_37])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (esk2_2(esk4_0,X1)=esk4_0|r2_hidden(esk2_2(esk4_0,X1),X1)|X1!=esk3_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_46, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_40])).
% 0.13/0.38  cnf(c_0_47, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_3(X1,X1,esk3_0),k2_tarski(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.13/0.38  cnf(c_0_49, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (esk2_2(esk4_0,esk3_0)=esk4_0|r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0)), inference(er,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_46])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (esk1_3(X1,X1,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.38  cnf(c_0_53, plain, (X2=k2_tarski(X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_49, c_0_8])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (esk2_2(esk4_0,esk3_0)=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_50]), c_0_47])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_44])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), c_0_38]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 57
% 0.13/0.38  # Proof object clause steps            : 46
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 23
% 0.13/0.38  # Proof object simplifying inferences  : 19
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 16
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 15
% 0.13/0.38  # Processed clauses                    : 112
% 0.13/0.38  # ...of these trivial                  : 7
% 0.13/0.38  # ...subsumed                          : 33
% 0.13/0.38  # ...remaining for further processing  : 72
% 0.13/0.38  # Other redundant clauses eliminated   : 18
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 6
% 0.13/0.38  # Backward-rewritten                   : 7
% 0.13/0.38  # Generated clauses                    : 534
% 0.13/0.38  # ...of the previous two non-trivial   : 420
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 498
% 0.13/0.38  # Factorizations                       : 4
% 0.13/0.38  # Equation resolutions                 : 30
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 56
% 0.13/0.38  #    Positive orientable unit clauses  : 13
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 39
% 0.13/0.38  # Current number of unprocessed clauses: 308
% 0.13/0.38  # ...number of literals in the above   : 1369
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 16
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 167
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 142
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 30
% 0.13/0.38  # Unit Clause-clause subsumption calls : 23
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 39
% 0.13/0.38  # BW rewrite match successes           : 7
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6831
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
