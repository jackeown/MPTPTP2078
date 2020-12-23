%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0634+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 47.02s
% Output     : CNFRefutation 47.02s
% Verified   : 
% Statistics : Number of formulae       :   32 (  40 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 (  92 expanded)
%              Number of equality atoms :   41 (  50 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f883,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1654,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f883])).

fof(f3605,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1654])).

fof(f879,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1649,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f879])).

fof(f3601,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1649])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2414,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f4319,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3601,f2414])).

fof(f924,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f925,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(negated_conjecture,[],[f924])).

fof(f1711,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f925])).

fof(f1712,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1711])).

fof(f2253,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k1_relat_1(sK194),sK193) != k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194))
      & v1_funct_1(sK194)
      & v1_relat_1(sK194) ) ),
    introduced(choice_axiom,[])).

fof(f2254,plain,
    ( k3_xboole_0(k1_relat_1(sK194),sK193) != k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194))
    & v1_funct_1(sK194)
    & v1_relat_1(sK194) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK193,sK194])],[f1712,f2253])).

fof(f3728,plain,(
    k3_xboole_0(k1_relat_1(sK194),sK193) != k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) ),
    inference(cnf_transformation,[],[f2254])).

fof(f4351,plain,(
    k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) != k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) ),
    inference(definition_unfolding,[],[f3728,f2414])).

fof(f3726,plain,(
    v1_relat_1(sK194) ),
    inference(cnf_transformation,[],[f2254])).

cnf(c_1332,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f3605])).

cnf(c_158822,plain,
    ( ~ v1_relat_1(sK194)
    | k5_relat_1(k6_relat_1(sK193),sK194) = k7_relat_1(sK194,sK193) ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_20009,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_72078,plain,
    ( k5_relat_1(k6_relat_1(sK193),sK194) != X0
    | k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_20009])).

cnf(c_158821,plain,
    ( k5_relat_1(k6_relat_1(sK193),sK194) != k7_relat_1(sK194,sK193)
    | k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) = k1_relat_1(k7_relat_1(sK194,sK193)) ),
    inference(instantiation,[status(thm)],[c_72078])).

cnf(c_1328,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4319])).

cnf(c_158580,plain,
    ( ~ v1_relat_1(sK194)
    | k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) = k1_relat_1(k7_relat_1(sK194,sK193)) ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_19954,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_54592,plain,
    ( k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) != X0
    | k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) = k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) != X0 ),
    inference(instantiation,[status(thm)],[c_19954])).

cnf(c_72077,plain,
    ( k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) != k1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) = k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_54592])).

cnf(c_158579,plain,
    ( k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) = k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194))
    | k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) != k1_relat_1(k7_relat_1(sK194,sK193))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) != k1_relat_1(k7_relat_1(sK194,sK193)) ),
    inference(instantiation,[status(thm)],[c_72077])).

cnf(c_1453,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(sK194),k4_xboole_0(k1_relat_1(sK194),sK193)) != k1_relat_1(k5_relat_1(k6_relat_1(sK193),sK194)) ),
    inference(cnf_transformation,[],[f4351])).

cnf(c_1455,negated_conjecture,
    ( v1_relat_1(sK194) ),
    inference(cnf_transformation,[],[f3726])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_158822,c_158821,c_158580,c_158579,c_1453,c_1455])).

%------------------------------------------------------------------------------
