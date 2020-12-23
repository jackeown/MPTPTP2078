%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0878+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:56 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 248 expanded)
%              Number of clauses        :   22 ( 109 expanded)
%              Number of leaves         :    8 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 515 expanded)
%              Number of equality atoms :   61 ( 428 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k3_zfmisc_1(X1,X1,X1) = k3_zfmisc_1(X2,X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t194_relat_1)).

fof(t115_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t115_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t195_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_zfmisc_1(X1,X1,X1) = k3_zfmisc_1(X2,X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t38_mcart_1])).

fof(c_0_9,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk1_0,esk1_0) = k3_zfmisc_1(esk2_0,esk2_0,esk2_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X15,X16,X17] : k3_zfmisc_1(X15,X16,X17) = k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X100,X101] :
      ( ( k2_zfmisc_1(X100,X101) != k1_xboole_0
        | X100 = k1_xboole_0
        | X101 = k1_xboole_0 )
      & ( X100 != k1_xboole_0
        | k2_zfmisc_1(X100,X101) = k1_xboole_0 )
      & ( X101 != k1_xboole_0
        | k2_zfmisc_1(X100,X101) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X221,X222] : r1_tarski(k2_relat_1(k2_zfmisc_1(X221,X222)),X222) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

cnf(c_0_13,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk1_0,esk1_0) = k3_zfmisc_1(esk2_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X104,X105] :
      ( k2_zfmisc_1(X104,X104) != k2_zfmisc_1(X105,X105)
      | X104 = X105 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_zfmisc_1])])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X1086,X1087] :
      ( ( r1_tarski(X1086,X1087)
        | X1086 != X1087 )
      & ( r1_tarski(X1087,X1086)
        | X1086 != X1087 )
      & ( ~ r1_tarski(X1086,X1087)
        | ~ r1_tarski(X1087,X1086)
        | X1086 = X1087 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

fof(c_0_20,plain,(
    ! [X223,X224] :
      ( ( k1_relat_1(k2_zfmisc_1(X223,X224)) = X223
        | X223 = k1_xboole_0
        | X224 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X223,X224)) = X224
        | X223 = k1_xboole_0
        | X224 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | k2_zfmisc_1(X1,X1) != k2_zfmisc_1(X2,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)) = esk1_0
    | ~ r1_tarski(esk1_0,k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_28]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

fof(c_0_32,plain,(
    ! [X296] : r1_tarski(k1_xboole_0,X296) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_34])])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_35]),c_0_34])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
