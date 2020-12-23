%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0486+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:41 EST 2020

% Result     : Theorem 15.20s
% Output     : CNFRefutation 15.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  30 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  48 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f711,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1244,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f711])).

fof(f1245,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1244])).

fof(f2801,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1245])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1695,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3349,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2801,f1695,f1695])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2731,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f715,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2807,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f715])).

fof(f725,conjecture,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f726,negated_conjecture,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f725])).

fof(f739,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f726])).

fof(f2823,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f739])).

fof(f3355,plain,(
    o_0_0_xboole_0 != k6_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2823,f1695,f1695])).

cnf(c_1098,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3349])).

cnf(c_54736,plain,
    ( ~ v1_relat_1(k6_relat_1(o_0_0_xboole_0))
    | k2_relat_1(k6_relat_1(o_0_0_xboole_0)) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k6_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1029,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2731])).

cnf(c_1360,plain,
    ( v1_relat_1(k6_relat_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1104,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2807])).

cnf(c_1166,plain,
    ( k2_relat_1(k6_relat_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_1121,negated_conjecture,
    ( o_0_0_xboole_0 != k6_relat_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3355])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54736,c_1360,c_1166,c_1121])).

%------------------------------------------------------------------------------
