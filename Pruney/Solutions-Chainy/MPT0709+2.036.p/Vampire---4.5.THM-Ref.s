%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:40 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 260 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  182 (1000 expanded)
%              Number of equality atoms :   52 ( 237 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f75,f130])).

fof(f130,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f128,f37])).

fof(f37,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f31])).

fof(f31,plain,
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

fof(f17,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f128,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f112,f125])).

fof(f125,plain,
    ( sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_1 ),
    inference(superposition,[],[f55,f105])).

fof(f105,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f84,f101])).

fof(f101,plain,(
    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f52,f61])).

fof(f61,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f60,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f35,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X1] : k3_xboole_0(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f84,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f83,f52])).

fof(f83,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f76,f51])).

fof(f51,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k2_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f76,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_1 ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f67,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_1
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f55,plain,(
    ! [X4,X5] : k10_relat_1(k7_relat_1(sK1,X4),X5) = k3_xboole_0(X4,k10_relat_1(sK1,X5)) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f112,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f108,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f57,f34])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f36,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k3_xboole_0(sK0,X0) = X0 )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f71,f104])).

fof(f104,plain,
    ( ! [X1] : k3_xboole_0(sK0,X1) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f89,f101])).

fof(f89,plain,
    ( ! [X1] : k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK1),sK0),X1)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f88,f52])).

fof(f88,plain,
    ( ! [X1] : k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X1) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f87,f52])).

fof(f87,plain,
    ( ! [X1] : k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X1) = k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,X1)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f78,f56])).

fof(f56,plain,(
    ! [X6,X7] : k7_relat_1(k7_relat_1(sK1,X6),X7) = k7_relat_1(sK1,k3_xboole_0(X6,X7)) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

% (11540)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f78,plain,
    ( ! [X1] : k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X1))
    | ~ spl2_1 ),
    inference(resolution,[],[f67,f42])).

fof(f71,plain,
    ( ! [X0] :
        ( k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0
        | ~ r1_tarski(X0,sK0) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_2
  <=> ! [X0] :
        ( k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f75,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f73,f33])).

fof(f73,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f68,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f72,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f64,f70,f66])).

fof(f64,plain,(
    ! [X0] :
      ( k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0
      | ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ) ),
    inference(forward_demodulation,[],[f63,f52])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,X0))) = X0
      | ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ) ),
    inference(forward_demodulation,[],[f62,f56])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = X0
      | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ) ),
    inference(superposition,[],[f45,f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:03:26 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.53  % (11548)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (11535)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (11543)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.53  % (11536)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.53  % (11537)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (11538)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.53  % (11543)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f131,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f72,f75,f130])).
% 1.25/0.53  fof(f130,plain,(
% 1.25/0.53    ~spl2_1 | ~spl2_2),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f129])).
% 1.25/0.53  fof(f129,plain,(
% 1.25/0.53    $false | (~spl2_1 | ~spl2_2)),
% 1.25/0.53    inference(subsumption_resolution,[],[f128,f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.25/0.53    inference(cnf_transformation,[],[f32])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.25/0.53    inference(flattening,[],[f16])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f14])).
% 1.25/0.53  fof(f14,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.25/0.53    inference(negated_conjecture,[],[f13])).
% 1.25/0.53  fof(f13,conjecture,(
% 1.25/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.25/0.53  fof(f128,plain,(
% 1.25/0.53    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_2)),
% 1.25/0.53    inference(backward_demodulation,[],[f112,f125])).
% 1.25/0.53  fof(f125,plain,(
% 1.25/0.53    sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_1),
% 1.25/0.53    inference(superposition,[],[f55,f105])).
% 1.25/0.53  fof(f105,plain,(
% 1.25/0.53    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_1),
% 1.25/0.53    inference(backward_demodulation,[],[f84,f101])).
% 1.25/0.53  fof(f101,plain,(
% 1.25/0.53    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 1.25/0.53    inference(superposition,[],[f52,f61])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.25/0.53    inference(subsumption_resolution,[],[f60,f33])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    v1_relat_1(sK1)),
% 1.25/0.53    inference(cnf_transformation,[],[f32])).
% 1.25/0.53  fof(f60,plain,(
% 1.25/0.53    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.25/0.53    inference(resolution,[],[f35,f45])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(flattening,[],[f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.25/0.53    inference(cnf_transformation,[],[f32])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X1] : (k3_xboole_0(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.25/0.53    inference(resolution,[],[f33,f42])).
% 1.25/0.53  fof(f42,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.25/0.53  fof(f84,plain,(
% 1.25/0.53    k3_xboole_0(k1_relat_1(sK1),sK0) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_1),
% 1.25/0.53    inference(forward_demodulation,[],[f83,f52])).
% 1.25/0.54  fof(f83,plain,(
% 1.25/0.54    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_1),
% 1.25/0.54    inference(forward_demodulation,[],[f76,f51])).
% 1.25/0.54  fof(f51,plain,(
% 1.25/0.54    ( ! [X0] : (k9_relat_1(sK1,X0) = k2_relat_1(k7_relat_1(sK1,X0))) )),
% 1.25/0.54    inference(resolution,[],[f33,f41])).
% 1.25/0.54  fof(f41,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f6])).
% 1.25/0.54  fof(f6,axiom,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.25/0.54  fof(f76,plain,(
% 1.25/0.54    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) | ~spl2_1),
% 1.25/0.54    inference(resolution,[],[f67,f38])).
% 1.25/0.54  fof(f38,plain,(
% 1.25/0.54    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f18])).
% 1.25/0.54  fof(f18,plain,(
% 1.25/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f7])).
% 1.25/0.54  fof(f7,axiom,(
% 1.25/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.25/0.54  fof(f67,plain,(
% 1.25/0.54    v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_1),
% 1.25/0.54    inference(avatar_component_clause,[],[f66])).
% 1.25/0.54  fof(f66,plain,(
% 1.25/0.54    spl2_1 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.25/0.54  fof(f55,plain,(
% 1.25/0.54    ( ! [X4,X5] : (k10_relat_1(k7_relat_1(sK1,X4),X5) = k3_xboole_0(X4,k10_relat_1(sK1,X5))) )),
% 1.25/0.54    inference(resolution,[],[f33,f48])).
% 1.25/0.54  fof(f48,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f29])).
% 1.25/0.54  fof(f29,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.25/0.54    inference(ennf_transformation,[],[f11])).
% 1.25/0.54  fof(f11,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.25/0.54  fof(f112,plain,(
% 1.25/0.54    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_1 | ~spl2_2)),
% 1.25/0.54    inference(resolution,[],[f108,f59])).
% 1.25/0.54  fof(f59,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.25/0.54    inference(subsumption_resolution,[],[f58,f33])).
% 1.25/0.54  fof(f58,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 1.25/0.54    inference(subsumption_resolution,[],[f57,f34])).
% 1.25/0.54  fof(f34,plain,(
% 1.25/0.54    v1_funct_1(sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f32])).
% 1.25/0.54  fof(f57,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.25/0.54    inference(resolution,[],[f36,f47])).
% 1.25/0.54  fof(f47,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f28])).
% 1.25/0.54  fof(f28,plain,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.54    inference(flattening,[],[f27])).
% 1.25/0.54  fof(f27,plain,(
% 1.25/0.54    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.54    inference(ennf_transformation,[],[f12])).
% 1.25/0.54  fof(f12,axiom,(
% 1.25/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.25/0.54  fof(f36,plain,(
% 1.25/0.54    v2_funct_1(sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f32])).
% 1.25/0.54  fof(f108,plain,(
% 1.25/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | k3_xboole_0(sK0,X0) = X0) ) | (~spl2_1 | ~spl2_2)),
% 1.25/0.54    inference(backward_demodulation,[],[f71,f104])).
% 1.25/0.54  fof(f104,plain,(
% 1.25/0.54    ( ! [X1] : (k3_xboole_0(sK0,X1) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1))) ) | ~spl2_1),
% 1.25/0.54    inference(backward_demodulation,[],[f89,f101])).
% 1.25/0.54  fof(f89,plain,(
% 1.25/0.54    ( ! [X1] : (k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK1),sK0),X1)) ) | ~spl2_1),
% 1.25/0.54    inference(forward_demodulation,[],[f88,f52])).
% 1.25/0.54  fof(f88,plain,(
% 1.25/0.54    ( ! [X1] : (k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X1) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1))) ) | ~spl2_1),
% 1.25/0.54    inference(forward_demodulation,[],[f87,f52])).
% 1.25/0.54  fof(f87,plain,(
% 1.25/0.54    ( ! [X1] : (k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X1) = k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,X1)))) ) | ~spl2_1),
% 1.25/0.54    inference(forward_demodulation,[],[f78,f56])).
% 1.25/0.54  fof(f56,plain,(
% 1.25/0.54    ( ! [X6,X7] : (k7_relat_1(k7_relat_1(sK1,X6),X7) = k7_relat_1(sK1,k3_xboole_0(X6,X7))) )),
% 1.25/0.54    inference(resolution,[],[f33,f49])).
% 1.25/0.54  fof(f49,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f30,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.25/0.54    inference(ennf_transformation,[],[f4])).
% 1.25/0.54  fof(f4,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.25/0.54  % (11540)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.54  fof(f78,plain,(
% 1.25/0.54    ( ! [X1] : (k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X1))) ) | ~spl2_1),
% 1.25/0.54    inference(resolution,[],[f67,f42])).
% 1.25/0.54  fof(f71,plain,(
% 1.25/0.54    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0 | ~r1_tarski(X0,sK0)) ) | ~spl2_2),
% 1.25/0.54    inference(avatar_component_clause,[],[f70])).
% 1.25/0.54  fof(f70,plain,(
% 1.25/0.54    spl2_2 <=> ! [X0] : (k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0 | ~r1_tarski(X0,sK0))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.25/0.54  fof(f75,plain,(
% 1.25/0.54    spl2_1),
% 1.25/0.54    inference(avatar_contradiction_clause,[],[f74])).
% 1.25/0.54  fof(f74,plain,(
% 1.25/0.54    $false | spl2_1),
% 1.25/0.54    inference(subsumption_resolution,[],[f73,f33])).
% 1.25/0.54  fof(f73,plain,(
% 1.25/0.54    ~v1_relat_1(sK1) | spl2_1),
% 1.25/0.54    inference(resolution,[],[f68,f40])).
% 1.25/0.54  fof(f40,plain,(
% 1.25/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f19])).
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.25/0.54  fof(f68,plain,(
% 1.25/0.54    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_1),
% 1.25/0.54    inference(avatar_component_clause,[],[f66])).
% 1.25/0.54  fof(f72,plain,(
% 1.25/0.54    ~spl2_1 | spl2_2),
% 1.25/0.54    inference(avatar_split_clause,[],[f64,f70,f66])).
% 1.25/0.54  fof(f64,plain,(
% 1.25/0.54    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0 | ~r1_tarski(X0,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0))) )),
% 1.25/0.54    inference(forward_demodulation,[],[f63,f52])).
% 1.25/0.54  fof(f63,plain,(
% 1.25/0.54    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,X0))) = X0 | ~r1_tarski(X0,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0))) )),
% 1.25/0.54    inference(forward_demodulation,[],[f62,f56])).
% 1.25/0.54  fof(f62,plain,(
% 1.25/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = X0 | ~v1_relat_1(k7_relat_1(sK1,sK0))) )),
% 1.25/0.54    inference(superposition,[],[f45,f61])).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (11543)------------------------------
% 1.25/0.54  % (11543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (11543)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (11543)Memory used [KB]: 10746
% 1.25/0.54  % (11543)Time elapsed: 0.124 s
% 1.25/0.54  % (11543)------------------------------
% 1.25/0.54  % (11543)------------------------------
% 1.25/0.54  % (11526)Success in time 0.178 s
%------------------------------------------------------------------------------
