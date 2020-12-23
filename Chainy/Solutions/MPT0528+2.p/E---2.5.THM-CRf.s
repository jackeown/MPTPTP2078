%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0528+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:47 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   25 (  36 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  67 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t128_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t128_relat_1])).

fof(c_0_7,plain,(
    ! [X2278,X2279] :
      ( ~ v1_relat_1(X2279)
      | k8_relat_1(X2278,X2279) = k5_relat_1(X2279,k6_relat_1(X2278)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk143_0)
    & k8_relat_1(esk142_0,k8_relat_1(esk142_0,esk143_0)) != k8_relat_1(esk142_0,esk143_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X2185,X2186] :
      ( ~ v1_relat_1(X2185)
      | ~ v1_relat_1(X2186)
      | v1_relat_1(k5_relat_1(X2185,X2186)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_10,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk143_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X2187] : v1_relat_1(k6_relat_1(X2187)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_13,plain,(
    ! [X2282,X2283] :
      ( ~ v1_relat_1(X2283)
      | ~ r1_tarski(k2_relat_1(X2283),X2282)
      | k8_relat_1(X2282,X2283) = X2283 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_14,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k5_relat_1(esk143_0,k6_relat_1(X1)) = k8_relat_1(X1,esk143_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X2262,X2263] :
      ( ~ v1_relat_1(X2263)
      | r1_tarski(k2_relat_1(k8_relat_1(X2262,X2263)),X2262) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

cnf(c_0_18,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk143_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X2,esk143_0)) = k8_relat_1(X2,esk143_0)
    | ~ r1_tarski(k2_relat_1(k8_relat_1(X2,esk143_0)),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k8_relat_1(esk142_0,k8_relat_1(esk142_0,esk143_0)) != k8_relat_1(esk142_0,esk143_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk143_0)),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_24,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_21,c_0_22,c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
