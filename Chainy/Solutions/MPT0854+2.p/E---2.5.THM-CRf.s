%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0854+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:54 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 216 expanded)
%              Number of clauses        :   32 ( 100 expanded)
%              Number of leaves         :    9 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  124 ( 486 expanded)
%              Number of equality atoms :   68 ( 217 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',d4_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',d5_relat_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t195_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t152_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t10_mcart_1])).

fof(c_0_10,plain,(
    ! [X135,X136,X137] :
      ( ~ r2_hidden(X135,k2_zfmisc_1(X136,X137))
      | k4_tarski(esk27_1(X135),esk28_1(X135)) = X135 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

fof(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))
    & ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
      | ~ r2_hidden(k2_mcart_1(esk1_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X633,X634] :
      ( k1_mcart_1(k4_tarski(X633,X634)) = X633
      & k2_mcart_1(k4_tarski(X633,X634)) = X634 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_13,plain,
    ( k4_tarski(esk27_1(X1),esk28_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(esk27_1(esk1_0),esk28_1(esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk27_1(esk1_0) = k1_mcart_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_18,plain,(
    ! [X400,X401,X402,X404,X405,X406,X407,X409] :
      ( ( ~ r2_hidden(X402,X401)
        | r2_hidden(k4_tarski(X402,esk59_3(X400,X401,X402)),X400)
        | X401 != k1_relat_1(X400) )
      & ( ~ r2_hidden(k4_tarski(X404,X405),X400)
        | r2_hidden(X404,X401)
        | X401 != k1_relat_1(X400) )
      & ( ~ r2_hidden(esk60_2(X406,X407),X407)
        | ~ r2_hidden(k4_tarski(esk60_2(X406,X407),X409),X406)
        | X407 = k1_relat_1(X406) )
      & ( r2_hidden(esk60_2(X406,X407),X407)
        | r2_hidden(k4_tarski(esk60_2(X406,X407),esk61_2(X406,X407)),X406)
        | X407 = k1_relat_1(X406) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_19,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),esk28_1(esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk28_1(esk1_0) = k2_mcart_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X411,X412,X413,X415,X416,X417,X418,X420] :
      ( ( ~ r2_hidden(X413,X412)
        | r2_hidden(k4_tarski(esk62_3(X411,X412,X413),X413),X411)
        | X412 != k2_relat_1(X411) )
      & ( ~ r2_hidden(k4_tarski(X416,X415),X411)
        | r2_hidden(X415,X412)
        | X412 != k2_relat_1(X411) )
      & ( ~ r2_hidden(esk63_2(X417,X418),X418)
        | ~ r2_hidden(k4_tarski(X420,esk63_2(X417,X418)),X417)
        | X418 = k2_relat_1(X417) )
      & ( r2_hidden(esk63_2(X417,X418),X418)
        | r2_hidden(k4_tarski(esk64_2(X417,X418),esk63_2(X417,X418)),X417)
        | X418 = k2_relat_1(X417) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),k1_relat_1(X1))
    | ~ r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_28,plain,(
    ! [X747,X748] :
      ( ( k1_relat_1(k2_zfmisc_1(X747,X748)) = X747
        | X747 = k1_xboole_0
        | X748 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X747,X748)) = X748
        | X747 = k1_xboole_0
        | X748 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_31,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X653,X654] :
      ( ( k2_zfmisc_1(X653,X654) != k1_xboole_0
        | X653 = k1_xboole_0
        | X654 = k1_xboole_0 )
      & ( X653 != k1_xboole_0
        | k2_zfmisc_1(X653,X654) = k1_xboole_0 )
      & ( X654 != k1_xboole_0
        | k2_zfmisc_1(X653,X654) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),k2_relat_1(X1))
    | ~ r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
    | ~ r2_hidden(k2_mcart_1(esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,plain,(
    ! [X232,X233] : ~ r2_hidden(X232,k2_zfmisc_1(X232,X233)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),k2_relat_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_39,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(k2_mcart_1(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_43]),c_0_42]),c_0_44])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_48,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_46]),c_0_47]),c_0_48]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
