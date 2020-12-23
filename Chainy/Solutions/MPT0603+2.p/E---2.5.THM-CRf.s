%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0603+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :   31 (  45 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 106 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t207_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t63_xboole_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_xboole_0(X1,X2)
         => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t207_relat_1])).

fof(c_0_8,plain,(
    ! [X332,X333,X334] :
      ( ~ r1_tarski(X332,X333)
      | ~ r1_xboole_0(X333,X334)
      | r1_xboole_0(X332,X334) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk157_0)
    & r1_xboole_0(esk155_0,esk156_0)
    & k7_relat_1(k7_relat_1(esk157_0,esk155_0),esk156_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X2667,X2668] :
      ( ~ v1_relat_1(X2668)
      | k7_relat_1(X2668,X2667) = k5_relat_1(k6_relat_1(X2667),X2668) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_11,plain,(
    ! [X2669,X2670] :
      ( ( k7_relat_1(X2670,X2669) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X2670),X2669)
        | ~ v1_relat_1(X2670) )
      & ( ~ r1_xboole_0(k1_relat_1(X2670),X2669)
        | k7_relat_1(X2670,X2669) = k1_xboole_0
        | ~ v1_relat_1(X2670) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(esk155_0,esk156_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X2216,X2217] :
      ( ~ v1_relat_1(X2216)
      | ~ v1_relat_1(X2217)
      | v1_relat_1(k5_relat_1(X2216,X2217)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_15,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk157_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X2218] : v1_relat_1(k6_relat_1(X2218)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_18,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(X1,esk156_0)
    | ~ r1_tarski(X1,esk155_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk157_0) = k7_relat_1(esk157_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X2651,X2652] :
      ( ~ v1_relat_1(X2652)
      | r1_tarski(k1_relat_1(k7_relat_1(X2652,X2651)),X2651) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_24,negated_conjecture,
    ( k7_relat_1(X1,esk156_0) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk155_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk157_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16]),c_0_22])])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk157_0,X1),esk156_0) = k1_xboole_0
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk157_0,X1)),esk155_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk157_0,esk155_0),esk156_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk157_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_30,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_27,c_0_28,c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
