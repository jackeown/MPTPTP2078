%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0876+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:56 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 923 expanded)
%              Number of clauses        :   51 ( 366 expanded)
%              Number of leaves         :    9 ( 244 expanded)
%              Depth                    :   20
%              Number of atoms          :  182 (3431 expanded)
%              Number of equality atoms :  157 (3237 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t195_relat_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t194_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t193_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_mcart_1])).

fof(c_0_10,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X239,X240,X241] : k3_zfmisc_1(X239,X240,X241) = k2_zfmisc_1(k2_zfmisc_1(X239,X240),X241) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X158,X159] :
      ( ( k1_relat_1(k2_zfmisc_1(X158,X159)) = X158
        | X158 = k1_xboole_0
        | X159 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X158,X159)) = X159
        | X158 = k1_xboole_0
        | X159 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_13,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X1402,X1403] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1402,X1403)),X1403) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

cnf(c_0_16,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) = k2_zfmisc_1(esk4_0,esk5_0)
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X56,X57] :
      ( ( k2_zfmisc_1(X56,X57) != k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 )
      & ( X57 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_22,plain,(
    ! [X1400,X1401] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1400,X1401)),X1400) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_24,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X1250,X1251] :
      ( ( r1_tarski(X1250,X1251)
        | X1250 != X1251 )
      & ( r1_tarski(X1251,X1250)
        | X1250 != X1251 )
      & ( ~ r1_tarski(X1250,X1251)
        | ~ r1_tarski(X1251,X1250)
        | X1250 = X1251 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | r1_tarski(esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20])).

cnf(c_0_30,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) = esk4_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_25]),c_0_26])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_29]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_33]),c_0_31]),c_0_32])).

fof(c_0_38,plain,(
    ! [X30] : r1_tarski(k1_xboole_0,X30) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) = k2_zfmisc_1(esk4_0,esk5_0)
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 = esk3_0
    | ~ r1_tarski(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 = esk1_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_37]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_20])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) = esk5_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) = esk6_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 = esk1_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_46]),c_0_42])])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_47]),c_0_31]),c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_48]),c_0_20])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_50]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = esk2_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_51]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = esk3_0
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_52]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != esk2_0
    | esk6_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_56]),c_0_42])]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_57]),c_0_30])]),c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = esk3_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_60]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_63]),c_0_42])]),c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_64]),c_0_46]),c_0_46]),c_0_42])])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_65]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_66]),c_0_53]),c_0_66]),c_0_53]),c_0_42])])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_67]),c_0_30])]),c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
