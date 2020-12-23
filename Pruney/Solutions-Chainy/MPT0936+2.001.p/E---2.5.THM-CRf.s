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
% DateTime   : Thu Dec  3 11:00:37 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 323 expanded)
%              Number of clauses        :   22 ( 127 expanded)
%              Number of leaves         :   11 (  99 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 420 expanded)
%              Number of equality atoms :   70 ( 389 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_mcart_1,conjecture,(
    ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t97_mcart_1])).

fof(c_0_12,plain,(
    ! [X94,X95] :
      ( ~ r1_xboole_0(k1_tarski(X94),k1_tarski(X95))
      | X94 != X95 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X70] : k2_tarski(X70,X70) = k1_tarski(X70) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X71,X72] : k2_enumset1(X71,X71,X71,X72) = k2_tarski(X71,X72) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_15,negated_conjecture,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk20_0,esk21_0,esk22_0)))) != k1_tarski(esk20_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X165,X166,X167] : k3_mcart_1(X165,X166,X167) = k4_tarski(k4_tarski(X165,X166),X167) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_17,plain,(
    ! [X106,X107] : k2_zfmisc_1(k1_tarski(X106),k1_tarski(X107)) = k1_tarski(k4_tarski(X106,X107)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

cnf(c_0_18,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk20_0,esk21_0,esk22_0)))) != k1_tarski(esk20_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_20]),c_0_20])).

fof(c_0_25,plain,(
    ! [X23] :
      ( ( r1_xboole_0(X23,X23)
        | X23 != k1_xboole_0 )
      & ( X23 = k1_xboole_0
        | ~ r1_xboole_0(X23,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_26,plain,(
    ! [X188,X189,X190] :
      ( ( X188 = k1_xboole_0
        | X189 = k1_xboole_0
        | X190 = k1_xboole_0
        | k3_zfmisc_1(X188,X189,X190) != k1_xboole_0 )
      & ( X188 != k1_xboole_0
        | k3_zfmisc_1(X188,X189,X190) = k1_xboole_0 )
      & ( X189 != k1_xboole_0
        | k3_zfmisc_1(X188,X189,X190) = k1_xboole_0 )
      & ( X190 != k1_xboole_0
        | k3_zfmisc_1(X188,X189,X190) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

fof(c_0_27,plain,(
    ! [X168,X169,X170] : k3_zfmisc_1(X168,X169,X170) = k2_zfmisc_1(k2_zfmisc_1(X168,X169),X170) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0),k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0),k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0),k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0)))) != k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

fof(c_0_30,plain,(
    ! [X156,X157] :
      ( ( k1_relat_1(k2_zfmisc_1(X156,X157)) = X156
        | X156 = k1_xboole_0
        | X157 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X156,X157)) = X157
        | X156 = k1_xboole_0
        | X157 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_31,plain,
    ( ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0)),k2_enumset1(esk22_0,esk22_0,esk22_0,esk22_0)))) != k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_36,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0)) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0))) != k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_38]),c_0_39]),c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_37]),c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_42]),c_0_39])]),c_0_41]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.50/0.71  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S033N
% 0.50/0.71  # and selection function PSelectUnlessUniqMax.
% 0.50/0.71  #
% 0.50/0.71  # Preprocessing time       : 0.034 s
% 0.50/0.71  # Presaturation interreduction done
% 0.50/0.71  
% 0.50/0.71  # Proof found!
% 0.50/0.71  # SZS status Theorem
% 0.50/0.71  # SZS output start CNFRefutation
% 0.50/0.71  fof(t97_mcart_1, conjecture, ![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 0.50/0.71  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.50/0.71  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.50/0.71  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.50/0.71  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.50/0.71  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.50/0.71  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.50/0.71  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.50/0.71  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.50/0.71  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.50/0.71  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.50/0.71  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t97_mcart_1])).
% 0.50/0.71  fof(c_0_12, plain, ![X94, X95]:(~r1_xboole_0(k1_tarski(X94),k1_tarski(X95))|X94!=X95), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.50/0.71  fof(c_0_13, plain, ![X70]:k2_tarski(X70,X70)=k1_tarski(X70), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.50/0.71  fof(c_0_14, plain, ![X71, X72]:k2_enumset1(X71,X71,X71,X72)=k2_tarski(X71,X72), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.50/0.71  fof(c_0_15, negated_conjecture, k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk20_0,esk21_0,esk22_0))))!=k1_tarski(esk20_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.50/0.71  fof(c_0_16, plain, ![X165, X166, X167]:k3_mcart_1(X165,X166,X167)=k4_tarski(k4_tarski(X165,X166),X167), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.50/0.71  fof(c_0_17, plain, ![X106, X107]:k2_zfmisc_1(k1_tarski(X106),k1_tarski(X107))=k1_tarski(k4_tarski(X106,X107)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.50/0.71  cnf(c_0_18, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.50/0.71  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.71  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.71  cnf(c_0_21, negated_conjecture, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk20_0,esk21_0,esk22_0))))!=k1_tarski(esk20_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.71  cnf(c_0_22, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.71  cnf(c_0_23, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.71  cnf(c_0_24, plain, (X1!=X2|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.50/0.71  fof(c_0_25, plain, ![X23]:((r1_xboole_0(X23,X23)|X23!=k1_xboole_0)&(X23=k1_xboole_0|~r1_xboole_0(X23,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.50/0.71  fof(c_0_26, plain, ![X188, X189, X190]:((X188=k1_xboole_0|X189=k1_xboole_0|X190=k1_xboole_0|k3_zfmisc_1(X188,X189,X190)!=k1_xboole_0)&(((X188!=k1_xboole_0|k3_zfmisc_1(X188,X189,X190)=k1_xboole_0)&(X189!=k1_xboole_0|k3_zfmisc_1(X188,X189,X190)=k1_xboole_0))&(X190!=k1_xboole_0|k3_zfmisc_1(X188,X189,X190)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.50/0.71  fof(c_0_27, plain, ![X168, X169, X170]:k3_zfmisc_1(X168,X169,X170)=k2_zfmisc_1(k2_zfmisc_1(X168,X169),X170), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.50/0.71  cnf(c_0_28, negated_conjecture, (k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0),k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0),k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0),k4_tarski(k4_tarski(esk20_0,esk21_0),esk22_0))))!=k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.50/0.71  cnf(c_0_29, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.50/0.71  fof(c_0_30, plain, ![X156, X157]:((k1_relat_1(k2_zfmisc_1(X156,X157))=X156|(X156=k1_xboole_0|X157=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X156,X157))=X157|(X156=k1_xboole_0|X157=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.50/0.71  cnf(c_0_31, plain, (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_24])).
% 0.50/0.71  cnf(c_0_32, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.71  cnf(c_0_33, plain, (k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.71  cnf(c_0_34, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.50/0.71  cnf(c_0_35, negated_conjecture, (k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0)),k2_enumset1(esk22_0,esk22_0,esk22_0,esk22_0))))!=k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 0.50/0.71  cnf(c_0_36, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.50/0.71  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.50/0.71  cnf(c_0_38, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.50/0.71  cnf(c_0_39, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.50/0.71  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0))=k1_xboole_0|k1_relat_1(k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0)))!=k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.50/0.71  cnf(c_0_41, negated_conjecture, (k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_38]), c_0_39]), c_0_39])])).
% 0.50/0.71  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(k2_enumset1(esk20_0,esk20_0,esk20_0,esk20_0),k2_enumset1(esk21_0,esk21_0,esk21_0,esk21_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_37]), c_0_41])).
% 0.50/0.71  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_42]), c_0_39])]), c_0_41]), c_0_37]), ['proof']).
% 0.50/0.71  # SZS output end CNFRefutation
% 0.50/0.71  # Proof object total steps             : 44
% 0.50/0.71  # Proof object clause steps            : 22
% 0.50/0.71  # Proof object formula steps           : 22
% 0.50/0.71  # Proof object conjectures             : 10
% 0.50/0.71  # Proof object clause conjectures      : 7
% 0.50/0.71  # Proof object formula conjectures     : 3
% 0.50/0.71  # Proof object initial clauses used    : 11
% 0.50/0.71  # Proof object initial formulas used   : 11
% 0.50/0.71  # Proof object generating inferences   : 5
% 0.50/0.71  # Proof object simplifying inferences  : 32
% 0.50/0.71  # Training examples: 0 positive, 0 negative
% 0.50/0.71  # Parsed axioms                        : 78
% 0.50/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.71  # Initial clauses                      : 149
% 0.50/0.71  # Removed in clause preprocessing      : 5
% 0.50/0.71  # Initial clauses in saturation        : 144
% 0.50/0.71  # Processed clauses                    : 4190
% 0.50/0.71  # ...of these trivial                  : 88
% 0.50/0.71  # ...subsumed                          : 3542
% 0.50/0.71  # ...remaining for further processing  : 560
% 0.50/0.71  # Other redundant clauses eliminated   : 40
% 0.50/0.71  # Clauses deleted for lack of memory   : 0
% 0.50/0.71  # Backward-subsumed                    : 5
% 0.50/0.71  # Backward-rewritten                   : 6
% 0.50/0.71  # Generated clauses                    : 42312
% 0.50/0.71  # ...of the previous two non-trivial   : 36725
% 0.50/0.71  # Contextual simplify-reflections      : 1
% 0.50/0.71  # Paramodulations                      : 42078
% 0.50/0.71  # Factorizations                       : 138
% 0.50/0.71  # Equation resolutions                 : 96
% 0.50/0.71  # Propositional unsat checks           : 0
% 0.50/0.71  #    Propositional check models        : 0
% 0.50/0.71  #    Propositional check unsatisfiable : 0
% 0.50/0.71  #    Propositional clauses             : 0
% 0.50/0.71  #    Propositional clauses after purity: 0
% 0.50/0.71  #    Propositional unsat core size     : 0
% 0.50/0.71  #    Propositional preprocessing time  : 0.000
% 0.50/0.71  #    Propositional encoding time       : 0.000
% 0.50/0.71  #    Propositional solver time         : 0.000
% 0.50/0.71  #    Success case prop preproc time    : 0.000
% 0.50/0.71  #    Success case prop encoding time   : 0.000
% 0.50/0.71  #    Success case prop solver time     : 0.000
% 0.50/0.71  # Current number of processed clauses  : 417
% 0.50/0.71  #    Positive orientable unit clauses  : 61
% 0.50/0.71  #    Positive unorientable unit clauses: 74
% 0.50/0.71  #    Negative unit clauses             : 20
% 0.50/0.71  #    Non-unit-clauses                  : 262
% 0.50/0.71  # Current number of unprocessed clauses: 32786
% 0.50/0.71  # ...number of literals in the above   : 61989
% 0.50/0.71  # Current number of archived formulas  : 0
% 0.50/0.71  # Current number of archived clauses   : 137
% 0.50/0.71  # Clause-clause subsumption calls (NU) : 17499
% 0.50/0.71  # Rec. Clause-clause subsumption calls : 12012
% 0.50/0.71  # Non-unit clause-clause subsumptions  : 949
% 0.50/0.71  # Unit Clause-clause subsumption calls : 2555
% 0.50/0.71  # Rewrite failures with RHS unbound    : 0
% 0.50/0.71  # BW rewrite match attempts            : 5630
% 0.50/0.71  # BW rewrite match successes           : 2959
% 0.50/0.71  # Condensation attempts                : 0
% 0.50/0.71  # Condensation successes               : 0
% 0.50/0.71  # Termbank termtop insertions          : 251261
% 0.50/0.71  
% 0.50/0.71  # -------------------------------------------------
% 0.50/0.71  # User time                : 0.350 s
% 0.50/0.71  # System time              : 0.013 s
% 0.50/0.71  # Total time               : 0.363 s
% 0.50/0.71  # Maximum resident set size: 1676 pages
%------------------------------------------------------------------------------
