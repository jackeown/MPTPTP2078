%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0486+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:46 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_relat_1,conjecture,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(c_0_4,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t81_relat_1])).

fof(c_0_5,plain,(
    ! [X2284] :
      ( ( k1_relat_1(X2284) != k1_xboole_0
        | X2284 = k1_xboole_0
        | ~ v1_relat_1(X2284) )
      & ( k2_relat_1(X2284) != k1_xboole_0
        | X2284 = k1_xboole_0
        | ~ v1_relat_1(X2284) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_6,plain,(
    ! [X2169] : v1_relat_1(k6_relat_1(X2169)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,plain,(
    ! [X2288] :
      ( k1_relat_1(k6_relat_1(X2288)) = X2288
      & k2_relat_1(k6_relat_1(X2288)) = X2288 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_8,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
