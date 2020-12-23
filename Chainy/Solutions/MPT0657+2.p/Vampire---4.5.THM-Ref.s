%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0657+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 322 expanded)
%              Number of leaves         :   11 ( 100 expanded)
%              Depth                    :   20
%              Number of atoms          :  301 (2338 expanded)
%              Number of equality atoms :   95 ( 873 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5418,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5399,f4649])).

fof(f4649,plain,(
    sK30 != k4_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f4648,f1862])).

fof(f1862,plain,(
    v1_relat_1(sK29) ),
    inference(cnf_transformation,[],[f1529])).

fof(f1529,plain,
    ( k2_funct_1(sK29) != sK30
    & k6_relat_1(k2_relat_1(sK29)) = k5_relat_1(sK30,sK29)
    & k1_relat_1(sK29) = k2_relat_1(sK30)
    & v2_funct_1(sK29)
    & v1_funct_1(sK30)
    & v1_relat_1(sK30)
    & v1_funct_1(sK29)
    & v1_relat_1(sK29) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29,sK30])],[f970,f1528,f1527])).

fof(f1527,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
            & k2_relat_1(X1) = k1_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK29) != X1
          & k5_relat_1(X1,sK29) = k6_relat_1(k2_relat_1(sK29))
          & k2_relat_1(X1) = k1_relat_1(sK29)
          & v2_funct_1(sK29)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK29)
      & v1_relat_1(sK29) ) ),
    introduced(choice_axiom,[])).

fof(f1528,plain,
    ( ? [X1] :
        ( k2_funct_1(sK29) != X1
        & k5_relat_1(X1,sK29) = k6_relat_1(k2_relat_1(sK29))
        & k2_relat_1(X1) = k1_relat_1(sK29)
        & v2_funct_1(sK29)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK29) != sK30
      & k6_relat_1(k2_relat_1(sK29)) = k5_relat_1(sK30,sK29)
      & k1_relat_1(sK29) = k2_relat_1(sK30)
      & v2_funct_1(sK29)
      & v1_funct_1(sK30)
      & v1_relat_1(sK30) ) ),
    introduced(choice_axiom,[])).

fof(f970,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f969])).

fof(f969,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f960])).

fof(f960,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f959])).

fof(f959,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f4648,plain,
    ( sK30 != k4_relat_1(sK29)
    | ~ v1_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f4647,f1863])).

fof(f1863,plain,(
    v1_funct_1(sK29) ),
    inference(cnf_transformation,[],[f1529])).

fof(f4647,plain,
    ( sK30 != k4_relat_1(sK29)
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f4625,f1866])).

fof(f1866,plain,(
    v2_funct_1(sK29) ),
    inference(cnf_transformation,[],[f1529])).

fof(f4625,plain,
    ( sK30 != k4_relat_1(sK29)
    | ~ v2_funct_1(sK29)
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29) ),
    inference(superposition,[],[f1869,f1902])).

fof(f1902,plain,(
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

fof(f1869,plain,(
    k2_funct_1(sK29) != sK30 ),
    inference(cnf_transformation,[],[f1529])).

fof(f5399,plain,(
    sK30 = k4_relat_1(sK29) ),
    inference(backward_demodulation,[],[f4082,f5387])).

fof(f5387,plain,(
    sK29 = k4_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f5367,f5137])).

fof(f5137,plain,(
    v2_funct_1(sK30) ),
    inference(subsumption_resolution,[],[f5136,f2900])).

fof(f2900,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2278])).

fof(f2278,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1739])).

fof(f1739,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1738])).

fof(f1738,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5136,plain,
    ( ~ r1_tarski(k2_relat_1(sK30),k2_relat_1(sK30))
    | v2_funct_1(sK30) ),
    inference(forward_demodulation,[],[f5135,f1867])).

fof(f1867,plain,(
    k1_relat_1(sK29) = k2_relat_1(sK30) ),
    inference(cnf_transformation,[],[f1529])).

fof(f5135,plain,
    ( v2_funct_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29)) ),
    inference(subsumption_resolution,[],[f5134,f1862])).

fof(f5134,plain,
    ( v2_funct_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29))
    | ~ v1_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f5133,f1863])).

fof(f5133,plain,
    ( v2_funct_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29))
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f5132,f1864])).

fof(f1864,plain,(
    v1_relat_1(sK30) ),
    inference(cnf_transformation,[],[f1529])).

fof(f5132,plain,
    ( v2_funct_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29))
    | ~ v1_relat_1(sK30)
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f5131,f1865])).

fof(f1865,plain,(
    v1_funct_1(sK30) ),
    inference(cnf_transformation,[],[f1529])).

fof(f5131,plain,
    ( v2_funct_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29))
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30)
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29) ),
    inference(subsumption_resolution,[],[f4895,f2012])).

fof(f2012,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f947])).

fof(f947,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f4895,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK29)))
    | v2_funct_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29))
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30)
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29) ),
    inference(superposition,[],[f1981,f1868])).

fof(f1868,plain,(
    k6_relat_1(k2_relat_1(sK29)) = k5_relat_1(sK30,sK29) ),
    inference(cnf_transformation,[],[f1529])).

fof(f1981,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1063])).

fof(f1063,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1062])).

fof(f1062,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f942])).

fof(f942,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(f5367,plain,
    ( sK29 = k4_relat_1(sK30)
    | ~ v2_funct_1(sK30) ),
    inference(backward_demodulation,[],[f5101,f5357])).

fof(f5357,plain,(
    k2_funct_1(sK30) = k4_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f5356,f1864])).

fof(f5356,plain,
    ( k2_funct_1(sK30) = k4_relat_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f5279,f1865])).

fof(f5279,plain,
    ( k2_funct_1(sK30) = k4_relat_1(sK30)
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(resolution,[],[f5137,f1902])).

fof(f5101,plain,
    ( sK29 = k2_funct_1(sK30)
    | ~ v2_funct_1(sK30) ),
    inference(trivial_inequality_removal,[],[f5100])).

fof(f5100,plain,
    ( k6_relat_1(k2_relat_1(sK29)) != k6_relat_1(k2_relat_1(sK29))
    | sK29 = k2_funct_1(sK30)
    | ~ v2_funct_1(sK30) ),
    inference(backward_demodulation,[],[f4946,f5000])).

fof(f5000,plain,(
    k2_relat_1(sK29) = k1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f4999,f2900])).

fof(f4999,plain,
    ( ~ r1_tarski(k2_relat_1(sK30),k2_relat_1(sK30))
    | k2_relat_1(sK29) = k1_relat_1(sK30) ),
    inference(forward_demodulation,[],[f4998,f1867])).

fof(f4998,plain,
    ( k2_relat_1(sK29) = k1_relat_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29)) ),
    inference(forward_demodulation,[],[f4997,f1938])).

fof(f1938,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f4997,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK29))) = k1_relat_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29)) ),
    inference(subsumption_resolution,[],[f4996,f1864])).

fof(f4996,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK29))) = k1_relat_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29))
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f4889,f1862])).

fof(f4889,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK29))) = k1_relat_1(sK30)
    | ~ r1_tarski(k2_relat_1(sK30),k1_relat_1(sK29))
    | ~ v1_relat_1(sK29)
    | ~ v1_relat_1(sK30) ),
    inference(superposition,[],[f1954,f1868])).

fof(f1954,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1036])).

fof(f1036,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1035])).

fof(f1035,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f845])).

fof(f845,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f4946,plain,
    ( k6_relat_1(k2_relat_1(sK29)) != k6_relat_1(k1_relat_1(sK30))
    | sK29 = k2_funct_1(sK30)
    | ~ v2_funct_1(sK30) ),
    inference(subsumption_resolution,[],[f4945,f1864])).

fof(f4945,plain,
    ( k6_relat_1(k2_relat_1(sK29)) != k6_relat_1(k1_relat_1(sK30))
    | sK29 = k2_funct_1(sK30)
    | ~ v2_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f4944,f1865])).

fof(f4944,plain,
    ( k6_relat_1(k2_relat_1(sK29)) != k6_relat_1(k1_relat_1(sK30))
    | sK29 = k2_funct_1(sK30)
    | ~ v2_funct_1(sK30)
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f4943,f1862])).

fof(f4943,plain,
    ( k6_relat_1(k2_relat_1(sK29)) != k6_relat_1(k1_relat_1(sK30))
    | sK29 = k2_funct_1(sK30)
    | ~ v2_funct_1(sK30)
    | ~ v1_relat_1(sK29)
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f4942,f1863])).

fof(f4942,plain,
    ( k6_relat_1(k2_relat_1(sK29)) != k6_relat_1(k1_relat_1(sK30))
    | sK29 = k2_funct_1(sK30)
    | ~ v2_funct_1(sK30)
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29)
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f4868,f1867])).

fof(f4868,plain,
    ( k6_relat_1(k2_relat_1(sK29)) != k6_relat_1(k1_relat_1(sK30))
    | sK29 = k2_funct_1(sK30)
    | k1_relat_1(sK29) != k2_relat_1(sK30)
    | ~ v2_funct_1(sK30)
    | ~ v1_funct_1(sK29)
    | ~ v1_relat_1(sK29)
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(superposition,[],[f1874,f1868])).

fof(f1874,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f976])).

fof(f976,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f975])).

fof(f975,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f958])).

fof(f958,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f4082,plain,(
    sK30 = k4_relat_1(k4_relat_1(sK30)) ),
    inference(resolution,[],[f1864,f2131])).

fof(f2131,plain,(
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
%------------------------------------------------------------------------------
