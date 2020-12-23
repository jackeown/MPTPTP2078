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
% DateTime   : Thu Dec  3 11:00:37 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 136 expanded)
%              Number of clauses        :   26 (  65 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 332 expanded)
%              Number of equality atoms :   60 ( 213 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t97_mcart_1,conjecture,(
    ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),k1_tarski(X16))) )
      & ( X14 = X16
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),k1_tarski(X16))) )
      & ( X13 != X15
        | X14 != X16
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),k1_tarski(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X17,X18] : k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18)) = k1_tarski(k4_tarski(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(k4_tarski(X21,esk2_3(X19,X20,X21)),X19)
        | X20 != k1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X19)
        | r2_hidden(X23,X20)
        | X20 != k1_relat_1(X19) )
      & ( ~ r2_hidden(esk3_2(X25,X26),X26)
        | ~ r2_hidden(k4_tarski(esk3_2(X25,X26),X28),X25)
        | X26 = k1_relat_1(X25) )
      & ( r2_hidden(esk3_2(X25,X26),X26)
        | r2_hidden(k4_tarski(esk3_2(X25,X26),esk4_2(X25,X26)),X25)
        | X26 = k1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_tarski(k4_tarski(X2,X4),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t97_mcart_1])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_11])).

fof(c_0_27,negated_conjecture,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0)))) != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_28,plain,(
    ! [X30,X31,X32] : k3_mcart_1(X30,X31,X32) = k4_tarski(k4_tarski(X30,X31),X32) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_29,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( esk1_2(X1,k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3)))) = X1
    | k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3))) = k2_tarski(X1,X1)
    | esk1_2(X1,k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3)))) = X2 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0)))) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_11])).

cnf(c_0_36,plain,
    ( esk1_2(X1,k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))) = X1
    | k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) = k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_30])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))) != k2_tarski(esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_11]),c_0_11]),c_0_34]),c_0_34])).

cnf(c_0_39,plain,
    ( k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) = k2_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.60/0.83  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.60/0.83  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.60/0.83  #
% 0.60/0.83  # Preprocessing time       : 0.027 s
% 0.60/0.83  # Presaturation interreduction done
% 0.60/0.83  
% 0.60/0.83  # Proof found!
% 0.60/0.83  # SZS status Theorem
% 0.60/0.83  # SZS output start CNFRefutation
% 0.60/0.83  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 0.60/0.83  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.60/0.83  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.60/0.83  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.60/0.83  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.60/0.83  fof(t97_mcart_1, conjecture, ![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 0.60/0.83  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.60/0.83  fof(c_0_7, plain, ![X13, X14, X15, X16]:(((X13=X15|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),k1_tarski(X16))))&(X14=X16|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),k1_tarski(X16)))))&(X13!=X15|X14!=X16|r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),k1_tarski(X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 0.60/0.83  fof(c_0_8, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.60/0.83  fof(c_0_9, plain, ![X17, X18]:k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18))=k1_tarski(k4_tarski(X17,X18)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.60/0.83  cnf(c_0_10, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.60/0.83  cnf(c_0_11, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.83  cnf(c_0_12, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.60/0.83  fof(c_0_13, plain, ![X19, X20, X21, X23, X24, X25, X26, X28]:(((~r2_hidden(X21,X20)|r2_hidden(k4_tarski(X21,esk2_3(X19,X20,X21)),X19)|X20!=k1_relat_1(X19))&(~r2_hidden(k4_tarski(X23,X24),X19)|r2_hidden(X23,X20)|X20!=k1_relat_1(X19)))&((~r2_hidden(esk3_2(X25,X26),X26)|~r2_hidden(k4_tarski(esk3_2(X25,X26),X28),X25)|X26=k1_relat_1(X25))&(r2_hidden(esk3_2(X25,X26),X26)|r2_hidden(k4_tarski(esk3_2(X25,X26),esk4_2(X25,X26)),X25)|X26=k1_relat_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.60/0.83  cnf(c_0_14, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.60/0.83  cnf(c_0_15, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_11]), c_0_11]), c_0_11])).
% 0.60/0.83  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.83  fof(c_0_17, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.60/0.83  cnf(c_0_18, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_tarski(k4_tarski(X2,X4),k4_tarski(X2,X4)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.60/0.83  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_16])).
% 0.60/0.83  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.60/0.83  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.60/0.83  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t97_mcart_1])).
% 0.60/0.83  cnf(c_0_23, plain, (X1=X2|~r2_hidden(X1,k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.60/0.83  cnf(c_0_24, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_20, c_0_11])).
% 0.60/0.83  cnf(c_0_25, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.83  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_21, c_0_11])).
% 0.60/0.83  fof(c_0_27, negated_conjecture, k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0))))!=k1_tarski(esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.60/0.83  fof(c_0_28, plain, ![X30, X31, X32]:k3_mcart_1(X30,X31,X32)=k4_tarski(k4_tarski(X30,X31),X32), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.60/0.83  cnf(c_0_29, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.60/0.83  cnf(c_0_30, plain, (esk1_2(X1,k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3))))=X1|k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3)))=k2_tarski(X1,X1)|esk1_2(X1,k1_relat_1(k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X3))))=X2), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.60/0.83  cnf(c_0_31, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_25])).
% 0.60/0.83  cnf(c_0_32, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.60/0.83  cnf(c_0_33, negated_conjecture, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0))))!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.60/0.83  cnf(c_0_34, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.83  cnf(c_0_35, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_29, c_0_11])).
% 0.60/0.83  cnf(c_0_36, plain, (esk1_2(X1,k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))))=X1|k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))=k2_tarski(X1,X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_30])])).
% 0.60/0.83  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.60/0.83  cnf(c_0_38, negated_conjecture, (k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))!=k2_tarski(esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_11]), c_0_11]), c_0_34]), c_0_34])).
% 0.60/0.83  cnf(c_0_39, plain, (k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))=k2_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.60/0.83  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39])]), ['proof']).
% 0.60/0.83  # SZS output end CNFRefutation
% 0.60/0.83  # Proof object total steps             : 41
% 0.60/0.83  # Proof object clause steps            : 26
% 0.60/0.83  # Proof object formula steps           : 15
% 0.60/0.83  # Proof object conjectures             : 6
% 0.60/0.83  # Proof object clause conjectures      : 3
% 0.60/0.83  # Proof object formula conjectures     : 3
% 0.60/0.83  # Proof object initial clauses used    : 10
% 0.60/0.83  # Proof object initial formulas used   : 7
% 0.60/0.83  # Proof object generating inferences   : 5
% 0.60/0.83  # Proof object simplifying inferences  : 23
% 0.60/0.83  # Training examples: 0 positive, 0 negative
% 0.60/0.83  # Parsed axioms                        : 7
% 0.60/0.83  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.83  # Initial clauses                      : 15
% 0.60/0.83  # Removed in clause preprocessing      : 2
% 0.60/0.83  # Initial clauses in saturation        : 13
% 0.60/0.83  # Processed clauses                    : 585
% 0.60/0.83  # ...of these trivial                  : 2
% 0.60/0.83  # ...subsumed                          : 140
% 0.60/0.83  # ...remaining for further processing  : 443
% 0.60/0.83  # Other redundant clauses eliminated   : 530
% 0.60/0.83  # Clauses deleted for lack of memory   : 0
% 0.60/0.83  # Backward-subsumed                    : 0
% 0.60/0.83  # Backward-rewritten                   : 127
% 0.60/0.83  # Generated clauses                    : 21002
% 0.60/0.83  # ...of the previous two non-trivial   : 20260
% 0.60/0.83  # Contextual simplify-reflections      : 0
% 0.60/0.83  # Paramodulations                      : 20448
% 0.60/0.83  # Factorizations                       : 19
% 0.60/0.83  # Equation resolutions                 : 537
% 0.60/0.83  # Propositional unsat checks           : 0
% 0.60/0.83  #    Propositional check models        : 0
% 0.60/0.83  #    Propositional check unsatisfiable : 0
% 0.60/0.83  #    Propositional clauses             : 0
% 0.60/0.83  #    Propositional clauses after purity: 0
% 0.60/0.83  #    Propositional unsat core size     : 0
% 0.60/0.83  #    Propositional preprocessing time  : 0.000
% 0.60/0.83  #    Propositional encoding time       : 0.000
% 0.60/0.83  #    Propositional solver time         : 0.000
% 0.60/0.83  #    Success case prop preproc time    : 0.000
% 0.60/0.83  #    Success case prop encoding time   : 0.000
% 0.60/0.83  #    Success case prop solver time     : 0.000
% 0.60/0.83  # Current number of processed clauses  : 299
% 0.60/0.83  #    Positive orientable unit clauses  : 3
% 0.60/0.83  #    Positive unorientable unit clauses: 0
% 0.60/0.83  #    Negative unit clauses             : 0
% 0.60/0.83  #    Non-unit-clauses                  : 296
% 0.60/0.83  # Current number of unprocessed clauses: 19591
% 0.60/0.83  # ...number of literals in the above   : 138279
% 0.60/0.83  # Current number of archived formulas  : 0
% 0.60/0.83  # Current number of archived clauses   : 141
% 0.60/0.83  # Clause-clause subsumption calls (NU) : 21860
% 0.60/0.83  # Rec. Clause-clause subsumption calls : 8582
% 0.60/0.83  # Non-unit clause-clause subsumptions  : 140
% 0.60/0.83  # Unit Clause-clause subsumption calls : 158
% 0.60/0.83  # Rewrite failures with RHS unbound    : 0
% 0.60/0.83  # BW rewrite match attempts            : 129
% 0.60/0.83  # BW rewrite match successes           : 26
% 0.60/0.83  # Condensation attempts                : 0
% 0.60/0.83  # Condensation successes               : 0
% 0.60/0.83  # Termbank termtop insertions          : 817663
% 0.60/0.83  
% 0.60/0.83  # -------------------------------------------------
% 0.60/0.83  # User time                : 0.469 s
% 0.60/0.83  # System time              : 0.017 s
% 0.60/0.83  # Total time               : 0.486 s
% 0.60/0.83  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
