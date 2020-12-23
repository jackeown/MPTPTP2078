%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 115 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  190 ( 426 expanded)
%              Number of equality atoms :   34 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f80,f82,f86,f111,f242,f326])).

fof(f326,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl3_6 ),
    inference(resolution,[],[f273,f26])).

fof(f26,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f273,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(trivial_inequality_removal,[],[f268])).

fof(f268,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f37,f106])).

fof(f106,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_6
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f242,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f237,f24])).

fof(f24,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f237,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | spl3_7 ),
    inference(resolution,[],[f144,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k6_subset_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | spl3_7 ),
    inference(resolution,[],[f110,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f110,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_7
  <=> r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f111,plain,
    ( ~ spl3_2
    | spl3_6
    | ~ spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f97,f63,f108,f104,f67])).

fof(f67,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( spl3_1
  <=> k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f97,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f29,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f86,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f77,f25])).

fof(f25,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f82,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f73,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f69,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f78,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f58,f75,f71,f67,f63])).

fof(f58,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f46,f23])).

fof(f23,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k9_relat_1(X3,X4),k9_relat_1(X3,X5))
      | ~ v2_funct_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_xboole_0 = k9_relat_1(X3,k6_subset_1(X4,X5)) ) ),
    inference(superposition,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:48:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (3064)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (3078)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (3066)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (3065)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (3067)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (3069)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (3066)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f327,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f78,f80,f82,f86,f111,f242,f326])).
% 0.22/0.48  fof(f326,plain,(
% 0.22/0.48    ~spl3_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f322])).
% 0.22/0.48  fof(f322,plain,(
% 0.22/0.48    $false | ~spl3_6),
% 0.22/0.48    inference(resolution,[],[f273,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ~r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.22/0.48  fof(f273,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1) | ~spl3_6),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f268])).
% 0.22/0.48  fof(f268,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl3_6),
% 0.22/0.48    inference(superposition,[],[f37,f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f104])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl3_6 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f31,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.48  fof(f242,plain,(
% 0.22/0.48    spl3_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.48  fof(f240,plain,(
% 0.22/0.48    $false | spl3_7),
% 0.22/0.48    inference(resolution,[],[f237,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f237,plain,(
% 0.22/0.48    ~r1_tarski(sK0,k1_relat_1(sK2)) | spl3_7),
% 0.22/0.48    inference(resolution,[],[f144,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f27,f28])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k6_subset_1(sK0,sK1),X0) | ~r1_tarski(X0,k1_relat_1(sK2))) ) | spl3_7),
% 0.22/0.48    inference(resolution,[],[f110,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(superposition,[],[f33,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl3_7 <=> r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ~spl3_2 | spl3_6 | ~spl3_7 | ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f97,f63,f108,f104,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl3_2 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl3_1 <=> k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.48    inference(superposition,[],[f29,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    $false | spl3_4),
% 0.22/0.48    inference(resolution,[],[f77,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v2_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ~v2_funct_1(sK2) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl3_4 <=> v2_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    $false | spl3_3),
% 0.22/0.48    inference(resolution,[],[f73,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ~v1_funct_1(sK2) | spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_3 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    $false | spl3_2),
% 0.22/0.48    inference(resolution,[],[f69,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f58,f75,f71,f67,f63])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f46,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~r1_tarski(k9_relat_1(X3,X4),k9_relat_1(X3,X5)) | ~v2_funct_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_xboole_0 = k9_relat_1(X3,k6_subset_1(X4,X5))) )),
% 0.22/0.48    inference(superposition,[],[f34,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f32,f28])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (3066)------------------------------
% 0.22/0.48  % (3066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3066)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (3066)Memory used [KB]: 6268
% 0.22/0.48  % (3066)Time elapsed: 0.063 s
% 0.22/0.48  % (3066)------------------------------
% 0.22/0.48  % (3066)------------------------------
% 0.22/0.48  % (3061)Success in time 0.12 s
%------------------------------------------------------------------------------
