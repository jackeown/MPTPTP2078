%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0658+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 298 expanded)
%              Number of leaves         :    6 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  131 (1129 expanded)
%              Number of equality atoms :   21 ( 270 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2619,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2618,f2038])).

fof(f2038,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2037,f2033])).

fof(f2033,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f2032,f1316])).

fof(f1316,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1183])).

fof(f1183,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f968,f1182])).

fof(f1182,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( sK0 != k2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f968,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f967])).

fof(f967,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f961])).

fof(f961,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f960])).

fof(f960,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f2032,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f1736,f1317])).

fof(f1317,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1183])).

fof(f1736,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f1315,f1351])).

fof(f1351,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f990])).

fof(f990,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f989])).

fof(f989,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f894])).

fof(f894,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f1315,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1183])).

fof(f2037,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f1738,f1316])).

fof(f1738,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f1315,f1353])).

fof(f1353,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f994])).

fof(f994,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f993])).

fof(f993,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f896,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f2618,plain,(
    ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2617,f2033])).

fof(f2617,plain,(
    ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f2616,f2040])).

fof(f2040,plain,(
    v1_funct_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2039,f2033])).

fof(f2039,plain,(
    v1_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f1739,f1316])).

fof(f1739,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f1315,f1354])).

fof(f1354,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f994])).

fof(f2616,plain,
    ( ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f2615,f2033])).

fof(f2615,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f2614,f2036])).

fof(f2036,plain,(
    v2_funct_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f2035,f2033])).

fof(f2035,plain,(
    v2_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f2034,f1316])).

fof(f2034,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f1737,f1317])).

fof(f1737,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f1315,f1352])).

fof(f1352,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f992])).

fof(f992,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f991])).

fof(f991,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f957])).

fof(f957,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f2614,plain,
    ( ~ v2_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f2613,f2033])).

fof(f2613,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f2612,f1940])).

fof(f1940,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f1315,f1569])).

fof(f1569,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1140])).

fof(f1140,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f700])).

fof(f700,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f2612,plain,
    ( sK0 != k4_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f2529,f2033])).

fof(f2529,plain,
    ( sK0 != k4_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(superposition,[],[f1318,f1351])).

fof(f1318,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f1183])).
%------------------------------------------------------------------------------
