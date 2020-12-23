%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 169 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  260 ( 503 expanded)
%              Number of equality atoms :   71 ( 133 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f605,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f75,f77,f86,f88,f165,f550,f597])).

fof(f597,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(trivial_inequality_removal,[],[f594])).

fof(f594,plain,
    ( k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(superposition,[],[f35,f565])).

fof(f565,plain,
    ( ! [X2] : k10_relat_1(k2_funct_1(sK1),X2) = k9_relat_1(sK1,X2)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f564,f154])).

fof(f154,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) ),
    inference(superposition,[],[f148,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f48,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f148,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f51,f48])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f564,plain,
    ( ! [X2] : k10_relat_1(k2_funct_1(sK1),X2) = k9_relat_1(sK1,k1_setfam_1(k2_tarski(X2,k1_relat_1(sK1))))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f555,f276])).

fof(f276,plain,
    ( ! [X5] : k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X5)) = k1_setfam_1(k2_tarski(X5,k1_relat_1(sK1)))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f275,f194])).

fof(f194,plain,(
    ! [X2,X1] : k1_setfam_1(k2_tarski(X2,X1)) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(forward_demodulation,[],[f193,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f193,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k6_relat_1(k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(forward_demodulation,[],[f192,f55])).

fof(f55,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f49,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f192,plain,(
    ! [X2,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(forward_demodulation,[],[f189,f38])).

fof(f189,plain,(
    ! [X2,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X2))) ),
    inference(resolution,[],[f98,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)) = k10_relat_1(k6_relat_1(X2),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f275,plain,
    ( ! [X5] : k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X5)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X5)
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f273,f164])).

fof(f164,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl2_12
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f273,plain,
    ( ! [X5] : k10_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)),X5) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X5))
    | ~ spl2_4 ),
    inference(resolution,[],[f258,f81])).

% (28447)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f81,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_4
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(sK1,X0),X1) = k10_relat_1(sK1,k10_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f555,plain,
    ( ! [X2] : k10_relat_1(k2_funct_1(sK1),X2) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2)))
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(resolution,[],[f549,f85])).

fof(f85,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_5
  <=> ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f549,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl2_19
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f35,plain,(
    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f550,plain,
    ( ~ spl2_1
    | spl2_19 ),
    inference(avatar_split_clause,[],[f545,f548,f62])).

fof(f62,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f545,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f165,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_12 ),
    inference(avatar_split_clause,[],[f156,f162,f66,f62])).

fof(f66,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f156,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f88,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f87,f80,f66,f62])).

fof(f87,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_4 ),
    inference(resolution,[],[f82,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f82,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f78,f70,f84,f80])).

fof(f70,plain,
    ( spl2_3
  <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f78,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl2_3 ),
    inference(superposition,[],[f50,f72])).

fof(f72,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f77,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f68,f33])).

fof(f68,plain,
    ( ~ v1_funct_1(sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f64,f32])).

fof(f64,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f73,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f58,f70,f66,f62])).

fof(f58,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (28442)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (28441)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (28454)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (28446)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (28443)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (28455)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (28449)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (28450)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (28451)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (28440)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (28452)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (28441)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (28456)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (28439)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (28445)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (28444)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (28453)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (28448)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f605,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f73,f75,f77,f86,f88,f165,f550,f597])).
% 0.21/0.50  fof(f597,plain,(
% 0.21/0.50    ~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_19),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f596])).
% 0.21/0.50  fof(f596,plain,(
% 0.21/0.50    $false | (~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_19)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f594])).
% 0.21/0.50  fof(f594,plain,(
% 0.21/0.50    k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) | (~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_19)),
% 0.21/0.50    inference(superposition,[],[f35,f565])).
% 0.21/0.50  fof(f565,plain,(
% 0.21/0.50    ( ! [X2] : (k10_relat_1(k2_funct_1(sK1),X2) = k9_relat_1(sK1,X2)) ) | (~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_19)),
% 0.21/0.50    inference(forward_demodulation,[],[f564,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))))) )),
% 0.21/0.50    inference(superposition,[],[f148,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f47,f48,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)))) )),
% 0.21/0.50    inference(resolution,[],[f56,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1] : ((k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f51,f48])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 0.21/0.50  fof(f564,plain,(
% 0.21/0.50    ( ! [X2] : (k10_relat_1(k2_funct_1(sK1),X2) = k9_relat_1(sK1,k1_setfam_1(k2_tarski(X2,k1_relat_1(sK1))))) ) | (~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_19)),
% 0.21/0.50    inference(forward_demodulation,[],[f555,f276])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    ( ! [X5] : (k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X5)) = k1_setfam_1(k2_tarski(X5,k1_relat_1(sK1)))) ) | (~spl2_4 | ~spl2_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f275,f194])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_setfam_1(k2_tarski(X2,X1)) = k10_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f193,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k6_relat_1(k1_setfam_1(k2_tarski(X2,X1))))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f192,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f49,f48])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f189,f38])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X2)))) )),
% 0.21/0.50    inference(resolution,[],[f98,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)) = k10_relat_1(k6_relat_1(X2),k1_relat_1(X1))) )),
% 0.21/0.50    inference(resolution,[],[f40,f36])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ( ! [X5] : (k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X5)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X5)) ) | (~spl2_4 | ~spl2_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f273,f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~spl2_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl2_12 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ( ! [X5] : (k10_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)),X5) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X5))) ) | ~spl2_4),
% 0.21/0.50    inference(resolution,[],[f258,f81])).
% 0.21/0.50  % (28447)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK1)) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl2_4 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(sK1,X0),X1) = k10_relat_1(sK1,k10_relat_1(X0,X1))) )),
% 0.21/0.50    inference(resolution,[],[f52,f32])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.21/0.50  fof(f555,plain,(
% 0.21/0.50    ( ! [X2] : (k10_relat_1(k2_funct_1(sK1),X2) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2)))) ) | (~spl2_5 | ~spl2_19)),
% 0.21/0.50    inference(resolution,[],[f549,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))) ) | ~spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl2_5 <=> ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f549,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) ) | ~spl2_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f548])).
% 0.21/0.50  fof(f548,plain,(
% 0.21/0.50    spl2_19 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f550,plain,(
% 0.21/0.50    ~spl2_1 | spl2_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f545,f548,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f545,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 0.21/0.50    inference(resolution,[],[f53,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2 | spl2_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f156,f162,f66,f62])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl2_2 <=> v1_funct_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f45,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v2_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2 | spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f87,f80,f66,f62])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_4),
% 0.21/0.50    inference(resolution,[],[f82,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK1)) | spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~spl2_4 | spl2_5 | ~spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f70,f84,f80])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl2_3 <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) ) | ~spl2_3),
% 0.21/0.50    inference(superposition,[],[f50,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    $false | spl2_2),
% 0.21/0.50    inference(resolution,[],[f68,f33])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    $false | spl2_1),
% 0.21/0.50    inference(resolution,[],[f64,f32])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2 | spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f70,f66,f62])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f43,f34])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28441)------------------------------
% 0.21/0.50  % (28441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28441)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28441)Memory used [KB]: 6524
% 0.21/0.50  % (28441)Time elapsed: 0.068 s
% 0.21/0.50  % (28441)------------------------------
% 0.21/0.50  % (28441)------------------------------
% 0.21/0.50  % (28438)Success in time 0.145 s
%------------------------------------------------------------------------------
