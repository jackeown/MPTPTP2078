%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:36 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 455 expanded)
%              Number of leaves         :   12 ( 110 expanded)
%              Depth                    :   25
%              Number of atoms          :  233 (1928 expanded)
%              Number of equality atoms :   59 ( 388 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f855,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f265,f851])).

fof(f851,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f850])).

fof(f850,plain,
    ( $false
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f844,f77])).

fof(f77,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f60])).

fof(f60,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f844,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f407,f75])).

fof(f75,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 )
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f406,f143])).

fof(f143,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(subsumption_resolution,[],[f142,f73])).

fof(f73,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f142,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f140,f74])).

fof(f74,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f140,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f76,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f76,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f406,plain,
    ( ! [X0] :
        ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = X0
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f405,f145])).

fof(f145,plain,(
    ! [X1] : k10_relat_1(sK1,X1) = k9_relat_1(k2_funct_1(sK1),X1) ),
    inference(subsumption_resolution,[],[f144,f73])).

fof(f144,plain,(
    ! [X1] :
      ( k10_relat_1(sK1,X1) = k9_relat_1(k2_funct_1(sK1),X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f141,f74])).

fof(f141,plain,(
    ! [X1] :
      ( k10_relat_1(sK1,X1) = k9_relat_1(k2_funct_1(sK1),X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f76,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f405,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0 )
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f404,f139])).

fof(f139,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f137,f73])).

fof(f137,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f74,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f404,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f403,f249])).

fof(f249,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_10
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0
        | ~ v1_funct_1(k2_funct_1(sK1))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl5_10 ),
    inference(superposition,[],[f99,f380])).

fof(f380,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f370,f287])).

fof(f287,plain,
    ( k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f286,f129])).

fof(f129,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f73,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f286,plain,
    ( k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f285,f143])).

fof(f285,plain,
    ( k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k1_relat_1(sK1)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f284,f139])).

fof(f284,plain,
    ( k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k1_relat_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f281,f249])).

fof(f281,plain,
    ( k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k1_relat_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f243,f99])).

fof(f243,plain,(
    r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1))) ),
    inference(superposition,[],[f154,f128])).

fof(f128,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f73,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f154,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK1,X1),k2_relat_1(k2_funct_1(sK1))) ),
    inference(forward_demodulation,[],[f149,f145])).

fof(f149,plain,(
    ! [X1] : r1_tarski(k9_relat_1(k2_funct_1(sK1),X1),k2_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f139,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f370,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f147,f366])).

fof(f366,plain,(
    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f362,f322])).

fof(f322,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f321,f131])).

fof(f131,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK1,X1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f73,f90])).

fof(f321,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))
    | ~ r1_tarski(k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))),k2_relat_1(sK1)) ),
    inference(resolution,[],[f299,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f65])).

% (13128)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f299,plain,(
    r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(superposition,[],[f156,f129])).

fof(f156,plain,(
    ! [X2] : r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(forward_demodulation,[],[f155,f143])).

fof(f155,plain,(
    ! [X2] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X2),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(forward_demodulation,[],[f150,f143])).

fof(f150,plain,(
    ! [X2] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X2),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))) ),
    inference(resolution,[],[f139,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f362,plain,(
    k1_relat_1(k2_funct_1(sK1)) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))) ),
    inference(superposition,[],[f143,f146])).

fof(f146,plain,(
    k1_relat_1(k2_funct_1(sK1)) = k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f139,f80])).

fof(f147,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f139,f81])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f265,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f263,f73])).

fof(f263,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f262,f74])).

fof(f262,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_10 ),
    inference(resolution,[],[f250,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f250,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n022.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 14:36:40 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.12/0.36  % (13121)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.12/0.36  % (13131)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.12/0.37  % (13137)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.12/0.37  % (13115)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.12/0.37  % (13139)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.12/0.37  % (13118)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.12/0.37  % (13123)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.12/0.37  % (13129)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.12/0.38  % (13116)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.12/0.38  % (13120)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.12/0.38  % (13122)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.12/0.38  % (13117)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.12/0.38  % (13135)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.12/0.39  % (13114)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.12/0.39  % (13127)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.12/0.40  % (13113)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.12/0.40  % (13133)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.12/0.40  % (13140)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.12/0.40  % (13142)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.12/0.40  % (13121)Refutation found. Thanks to Tanya!
% 0.12/0.40  % SZS status Theorem for theBenchmark
% 0.12/0.40  % (13141)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.12/0.40  % (13124)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.12/0.41  % (13132)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.12/0.41  % (13119)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.12/0.41  % (13126)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.12/0.41  % (13125)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.41  % (13136)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.12/0.42  % (13134)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.12/0.42  % SZS output start Proof for theBenchmark
% 0.12/0.42  fof(f855,plain,(
% 0.12/0.42    $false),
% 0.12/0.42    inference(avatar_sat_refutation,[],[f265,f851])).
% 0.12/0.42  fof(f851,plain,(
% 0.12/0.42    ~spl5_10),
% 0.12/0.42    inference(avatar_contradiction_clause,[],[f850])).
% 0.12/0.42  fof(f850,plain,(
% 0.12/0.42    $false | ~spl5_10),
% 0.12/0.42    inference(subsumption_resolution,[],[f844,f77])).
% 0.12/0.42  fof(f77,plain,(
% 0.12/0.42    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.12/0.42    inference(cnf_transformation,[],[f61])).
% 0.12/0.42  fof(f61,plain,(
% 0.12/0.42    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.12/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f60])).
% 0.12/0.42  fof(f60,plain,(
% 0.12/0.42    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.12/0.42    introduced(choice_axiom,[])).
% 0.12/0.42  fof(f34,plain,(
% 0.12/0.42    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.12/0.42    inference(flattening,[],[f33])).
% 0.12/0.42  fof(f33,plain,(
% 0.12/0.42    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.12/0.42    inference(ennf_transformation,[],[f31])).
% 0.12/0.42  fof(f31,negated_conjecture,(
% 0.12/0.42    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.12/0.42    inference(negated_conjecture,[],[f30])).
% 0.12/0.42  fof(f30,conjecture,(
% 0.12/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.12/0.42  fof(f844,plain,(
% 0.12/0.42    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | ~spl5_10),
% 0.12/0.42    inference(resolution,[],[f407,f75])).
% 0.12/0.42  fof(f75,plain,(
% 0.12/0.42    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.12/0.42    inference(cnf_transformation,[],[f61])).
% 0.12/0.42  fof(f407,plain,(
% 0.12/0.42    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) ) | ~spl5_10),
% 0.12/0.42    inference(forward_demodulation,[],[f406,f143])).
% 0.12/0.42  fof(f143,plain,(
% 0.12/0.42    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) )),
% 0.12/0.42    inference(subsumption_resolution,[],[f142,f73])).
% 0.12/0.42  fof(f73,plain,(
% 0.12/0.42    v1_relat_1(sK1)),
% 0.12/0.42    inference(cnf_transformation,[],[f61])).
% 0.12/0.42  fof(f142,plain,(
% 0.12/0.42    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.12/0.42    inference(subsumption_resolution,[],[f140,f74])).
% 0.12/0.42  fof(f74,plain,(
% 0.12/0.42    v1_funct_1(sK1)),
% 0.12/0.42    inference(cnf_transformation,[],[f61])).
% 0.12/0.42  fof(f140,plain,(
% 0.12/0.42    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.12/0.42    inference(resolution,[],[f76,f98])).
% 0.12/0.42  fof(f98,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f52])).
% 0.12/0.42  fof(f52,plain,(
% 0.12/0.42    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.12/0.42    inference(flattening,[],[f51])).
% 0.12/0.42  fof(f51,plain,(
% 0.12/0.42    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.12/0.42    inference(ennf_transformation,[],[f28])).
% 0.12/0.42  fof(f28,axiom,(
% 0.12/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.12/0.42  fof(f76,plain,(
% 0.12/0.42    v2_funct_1(sK1)),
% 0.12/0.42    inference(cnf_transformation,[],[f61])).
% 0.12/0.42  fof(f406,plain,(
% 0.12/0.42    ( ! [X0] : (k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl5_10),
% 0.12/0.42    inference(forward_demodulation,[],[f405,f145])).
% 0.12/0.42  fof(f145,plain,(
% 0.12/0.42    ( ! [X1] : (k10_relat_1(sK1,X1) = k9_relat_1(k2_funct_1(sK1),X1)) )),
% 0.12/0.42    inference(subsumption_resolution,[],[f144,f73])).
% 0.12/0.42  fof(f144,plain,(
% 0.12/0.42    ( ! [X1] : (k10_relat_1(sK1,X1) = k9_relat_1(k2_funct_1(sK1),X1) | ~v1_relat_1(sK1)) )),
% 0.12/0.42    inference(subsumption_resolution,[],[f141,f74])).
% 0.12/0.42  fof(f141,plain,(
% 0.12/0.42    ( ! [X1] : (k10_relat_1(sK1,X1) = k9_relat_1(k2_funct_1(sK1),X1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.12/0.42    inference(resolution,[],[f76,f97])).
% 0.12/0.42  fof(f97,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f50])).
% 0.12/0.42  fof(f50,plain,(
% 0.12/0.42    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.12/0.42    inference(flattening,[],[f49])).
% 0.12/0.42  fof(f49,plain,(
% 0.12/0.42    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.12/0.42    inference(ennf_transformation,[],[f29])).
% 0.12/0.42  fof(f29,axiom,(
% 0.12/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.12/0.42  fof(f405,plain,(
% 0.12/0.42    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0) ) | ~spl5_10),
% 0.12/0.42    inference(subsumption_resolution,[],[f404,f139])).
% 0.12/0.42  fof(f139,plain,(
% 0.12/0.42    v1_relat_1(k2_funct_1(sK1))),
% 0.12/0.42    inference(subsumption_resolution,[],[f137,f73])).
% 0.12/0.42  fof(f137,plain,(
% 0.12/0.42    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.12/0.42    inference(resolution,[],[f74,f82])).
% 0.12/0.42  fof(f82,plain,(
% 0.12/0.42    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f38])).
% 0.12/0.42  fof(f38,plain,(
% 0.12/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.12/0.42    inference(flattening,[],[f37])).
% 0.12/0.42  fof(f37,plain,(
% 0.12/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.12/0.42    inference(ennf_transformation,[],[f24])).
% 0.12/0.42  fof(f24,axiom,(
% 0.12/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.12/0.42  fof(f404,plain,(
% 0.12/0.42    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~v1_relat_1(k2_funct_1(sK1))) ) | ~spl5_10),
% 0.12/0.42    inference(subsumption_resolution,[],[f403,f249])).
% 0.12/0.42  fof(f249,plain,(
% 0.12/0.42    v1_funct_1(k2_funct_1(sK1)) | ~spl5_10),
% 0.12/0.42    inference(avatar_component_clause,[],[f248])).
% 0.12/0.42  fof(f248,plain,(
% 0.12/0.42    spl5_10 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.12/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.12/0.42  fof(f403,plain,(
% 0.12/0.42    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) ) | ~spl5_10),
% 0.12/0.42    inference(superposition,[],[f99,f380])).
% 0.12/0.42  fof(f380,plain,(
% 0.12/0.42    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~spl5_10),
% 0.12/0.42    inference(forward_demodulation,[],[f370,f287])).
% 0.12/0.42  fof(f287,plain,(
% 0.12/0.42    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) | ~spl5_10),
% 0.12/0.42    inference(forward_demodulation,[],[f286,f129])).
% 0.12/0.42  fof(f129,plain,(
% 0.12/0.42    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.12/0.42    inference(resolution,[],[f73,f81])).
% 0.12/0.42  fof(f81,plain,(
% 0.12/0.42    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f36])).
% 0.12/0.42  fof(f36,plain,(
% 0.12/0.42    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f16])).
% 0.12/0.42  fof(f16,axiom,(
% 0.12/0.42    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.12/0.42  fof(f286,plain,(
% 0.12/0.42    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) | ~spl5_10),
% 0.12/0.42    inference(forward_demodulation,[],[f285,f143])).
% 0.12/0.42  fof(f285,plain,(
% 0.12/0.42    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k1_relat_1(sK1))) | ~spl5_10),
% 0.12/0.42    inference(subsumption_resolution,[],[f284,f139])).
% 0.12/0.42  fof(f284,plain,(
% 0.12/0.42    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k1_relat_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl5_10),
% 0.12/0.42    inference(subsumption_resolution,[],[f281,f249])).
% 0.12/0.42  fof(f281,plain,(
% 0.12/0.42    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k1_relat_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.12/0.42    inference(resolution,[],[f243,f99])).
% 0.12/0.42  fof(f243,plain,(
% 0.12/0.42    r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1)))),
% 0.12/0.42    inference(superposition,[],[f154,f128])).
% 0.12/0.42  fof(f128,plain,(
% 0.12/0.42    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.12/0.42    inference(resolution,[],[f73,f80])).
% 0.12/0.42  fof(f80,plain,(
% 0.12/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f35])).
% 0.12/0.42  fof(f35,plain,(
% 0.12/0.42    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f20])).
% 0.12/0.42  fof(f20,axiom,(
% 0.12/0.42    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.12/0.42  fof(f154,plain,(
% 0.12/0.42    ( ! [X1] : (r1_tarski(k10_relat_1(sK1,X1),k2_relat_1(k2_funct_1(sK1)))) )),
% 0.12/0.42    inference(forward_demodulation,[],[f149,f145])).
% 0.12/0.42  fof(f149,plain,(
% 0.12/0.42    ( ! [X1] : (r1_tarski(k9_relat_1(k2_funct_1(sK1),X1),k2_relat_1(k2_funct_1(sK1)))) )),
% 0.12/0.42    inference(resolution,[],[f139,f90])).
% 0.12/0.42  fof(f90,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f41])).
% 0.12/0.42  fof(f41,plain,(
% 0.12/0.42    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.12/0.42    inference(ennf_transformation,[],[f15])).
% 0.12/0.42  fof(f15,axiom,(
% 0.12/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.12/0.42  fof(f370,plain,(
% 0.12/0.42    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1))),
% 0.12/0.42    inference(backward_demodulation,[],[f147,f366])).
% 0.12/0.42  fof(f366,plain,(
% 0.12/0.42    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.12/0.42    inference(forward_demodulation,[],[f362,f322])).
% 0.12/0.42  fof(f322,plain,(
% 0.12/0.42    k2_relat_1(sK1) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))),
% 0.12/0.42    inference(subsumption_resolution,[],[f321,f131])).
% 0.12/0.42  fof(f131,plain,(
% 0.12/0.42    ( ! [X1] : (r1_tarski(k9_relat_1(sK1,X1),k2_relat_1(sK1))) )),
% 0.12/0.42    inference(resolution,[],[f73,f90])).
% 0.12/0.42  fof(f321,plain,(
% 0.12/0.42    k2_relat_1(sK1) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))) | ~r1_tarski(k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))),k2_relat_1(sK1))),
% 0.12/0.42    inference(resolution,[],[f299,f102])).
% 0.12/0.42  fof(f102,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f66])).
% 0.12/0.42  fof(f66,plain,(
% 0.12/0.42    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.42    inference(flattening,[],[f65])).
% 0.12/0.42  % (13128)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.12/0.42  fof(f65,plain,(
% 0.12/0.42    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.42    inference(nnf_transformation,[],[f4])).
% 0.12/0.42  fof(f4,axiom,(
% 0.12/0.42    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.12/0.42  fof(f299,plain,(
% 0.12/0.42    r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))),
% 0.12/0.42    inference(superposition,[],[f156,f129])).
% 0.12/0.42  fof(f156,plain,(
% 0.12/0.42    ( ! [X2] : (r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))) )),
% 0.12/0.42    inference(forward_demodulation,[],[f155,f143])).
% 0.12/0.42  fof(f155,plain,(
% 0.12/0.42    ( ! [X2] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X2),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))) )),
% 0.12/0.42    inference(forward_demodulation,[],[f150,f143])).
% 0.12/0.42  fof(f150,plain,(
% 0.12/0.42    ( ! [X2] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X2),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))))) )),
% 0.12/0.42    inference(resolution,[],[f139,f91])).
% 0.12/0.42  fof(f91,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f42])).
% 0.12/0.42  fof(f42,plain,(
% 0.12/0.42    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.12/0.42    inference(ennf_transformation,[],[f21])).
% 0.12/0.42  fof(f21,axiom,(
% 0.12/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 0.12/0.42  fof(f362,plain,(
% 0.12/0.42    k1_relat_1(k2_funct_1(sK1)) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))),
% 0.12/0.42    inference(superposition,[],[f143,f146])).
% 0.12/0.42  fof(f146,plain,(
% 0.12/0.42    k1_relat_1(k2_funct_1(sK1)) = k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))),
% 0.12/0.42    inference(resolution,[],[f139,f80])).
% 0.12/0.42  fof(f147,plain,(
% 0.12/0.42    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.12/0.42    inference(resolution,[],[f139,f81])).
% 0.12/0.42  fof(f99,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f54])).
% 0.12/0.42  fof(f54,plain,(
% 0.12/0.42    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.12/0.42    inference(flattening,[],[f53])).
% 0.12/0.42  fof(f53,plain,(
% 0.12/0.42    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.12/0.42    inference(ennf_transformation,[],[f27])).
% 0.12/0.42  fof(f27,axiom,(
% 0.12/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.12/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.12/0.42  fof(f265,plain,(
% 0.12/0.42    spl5_10),
% 0.12/0.42    inference(avatar_contradiction_clause,[],[f264])).
% 0.12/0.42  fof(f264,plain,(
% 0.12/0.42    $false | spl5_10),
% 0.12/0.42    inference(subsumption_resolution,[],[f263,f73])).
% 0.12/0.42  fof(f263,plain,(
% 0.12/0.42    ~v1_relat_1(sK1) | spl5_10),
% 0.12/0.42    inference(subsumption_resolution,[],[f262,f74])).
% 0.12/0.42  fof(f262,plain,(
% 0.12/0.42    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl5_10),
% 0.12/0.42    inference(resolution,[],[f250,f83])).
% 0.12/0.42  fof(f83,plain,(
% 0.12/0.42    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f38])).
% 0.12/0.42  fof(f250,plain,(
% 0.12/0.42    ~v1_funct_1(k2_funct_1(sK1)) | spl5_10),
% 0.12/0.42    inference(avatar_component_clause,[],[f248])).
% 0.12/0.42  % SZS output end Proof for theBenchmark
% 0.12/0.42  % (13121)------------------------------
% 0.12/0.42  % (13121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (13121)Termination reason: Refutation
% 0.12/0.42  
% 0.12/0.42  % (13121)Memory used [KB]: 11257
% 0.12/0.42  % (13121)Time elapsed: 0.080 s
% 0.12/0.42  % (13121)------------------------------
% 0.12/0.42  % (13121)------------------------------
% 0.12/0.42  % (13138)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.12/0.42  % (13112)Success in time 0.145 s
%------------------------------------------------------------------------------
