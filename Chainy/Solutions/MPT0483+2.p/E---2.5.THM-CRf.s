%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0483+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:46 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   14 (  17 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t78_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    inference(assume_negation,[status(cth)],[t78_relat_1])).

fof(c_0_4,plain,(
    ! [X2303,X2304] :
      ( ~ v1_relat_1(X2304)
      | ~ r1_tarski(k1_relat_1(X2304),X2303)
      | k5_relat_1(k6_relat_1(X2303),X2304) = X2304 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk143_0)
    & k5_relat_1(k6_relat_1(k1_relat_1(esk143_0)),esk143_0) != esk143_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_7,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk143_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk143_0) = esk143_0
    | ~ r1_tarski(k1_relat_1(esk143_0),X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk143_0)),esk143_0) != esk143_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
