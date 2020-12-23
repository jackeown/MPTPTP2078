%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  98 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  174 ( 254 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (29137)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
fof(f158,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f37,f41,f45,f49,f53,f60,f75,f97,f130,f151])).

fof(f151,plain,
    ( spl2_1
    | ~ spl2_20 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl2_1
    | ~ spl2_20 ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1)
    | spl2_1
    | ~ spl2_20 ),
    inference(superposition,[],[f27,f129])).

fof(f129,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl2_20
  <=> ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f27,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f130,plain,
    ( spl2_20
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f126,f95,f73,f30,f128])).

fof(f30,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f73,plain,
    ( spl2_11
  <=> ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f126,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f122,f32])).

fof(f32,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f122,plain,
    ( ! [X0] :
        ( k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(resolution,[],[f96,f74])).

fof(f74,plain,
    ( ! [X0] : v1_relat_1(k8_relat_1(X0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k8_relat_1(X0,X1))
        | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f93,f47,f39,f95])).

fof(f39,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f47,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
        | ~ v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f75,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f71,f58,f51,f35,f30,f73])).

fof(f35,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f51,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f58,plain,
    ( spl2_8
  <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f71,plain,
    ( ! [X0] : v1_relat_1(k8_relat_1(X0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f70,f32])).

fof(f70,plain,
    ( ! [X0] :
        ( v1_relat_1(k8_relat_1(X0,sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f69,f36])).

fof(f36,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f69,plain,
    ( ! [X0] :
        ( v1_relat_1(k8_relat_1(X0,sK1))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(superposition,[],[f52,f59])).

fof(f59,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f60,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f54,f43,f30,f58])).

fof(f43,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f54,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f53,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f49,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f45,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f41,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f37,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (29138)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.41  % (29138)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  % (29137)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.41  fof(f158,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f28,f33,f37,f41,f45,f49,f53,f60,f75,f97,f130,f151])).
% 0.21/0.41  fof(f151,plain,(
% 0.21/0.41    spl2_1 | ~spl2_20),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.41  fof(f150,plain,(
% 0.21/0.41    $false | (spl2_1 | ~spl2_20)),
% 0.21/0.41    inference(trivial_inequality_removal,[],[f149])).
% 0.21/0.41  fof(f149,plain,(
% 0.21/0.41    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) | (spl2_1 | ~spl2_20)),
% 0.21/0.41    inference(superposition,[],[f27,f129])).
% 0.21/0.41  fof(f129,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))) ) | ~spl2_20),
% 0.21/0.41    inference(avatar_component_clause,[],[f128])).
% 0.21/0.41  fof(f128,plain,(
% 0.21/0.41    spl2_20 <=> ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) | spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    spl2_1 <=> k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f130,plain,(
% 0.21/0.41    spl2_20 | ~spl2_2 | ~spl2_11 | ~spl2_15),
% 0.21/0.41    inference(avatar_split_clause,[],[f126,f95,f73,f30,f128])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    spl2_11 <=> ! [X0] : v1_relat_1(k8_relat_1(X0,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    spl2_15 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.41  fof(f126,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))) ) | (~spl2_2 | ~spl2_11 | ~spl2_15)),
% 0.21/0.41    inference(subsumption_resolution,[],[f122,f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f30])).
% 0.21/0.41  fof(f122,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1)) | ~v1_relat_1(sK1)) ) | (~spl2_11 | ~spl2_15)),
% 0.21/0.41    inference(resolution,[],[f96,f74])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1))) ) | ~spl2_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f73])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl2_15),
% 0.21/0.41    inference(avatar_component_clause,[],[f95])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    spl2_15 | ~spl2_4 | ~spl2_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f93,f47,f39,f95])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    spl2_4 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    spl2_6 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.41  fof(f93,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.41    inference(resolution,[],[f48,f40])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) ) | ~spl2_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f39])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl2_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f47])).
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    spl2_11 | ~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f71,f58,f51,f35,f30,f73])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    spl2_7 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    spl2_8 <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1))) ) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_8)),
% 0.21/0.41    inference(subsumption_resolution,[],[f70,f32])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1)) | ~v1_relat_1(sK1)) ) | (~spl2_3 | ~spl2_7 | ~spl2_8)),
% 0.21/0.41    inference(subsumption_resolution,[],[f69,f36])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f35])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) ) | (~spl2_7 | ~spl2_8)),
% 0.21/0.41    inference(superposition,[],[f52,f59])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl2_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f58])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f51])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl2_8 | ~spl2_2 | ~spl2_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f54,f43,f30,f58])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl2_5 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_5)),
% 0.21/0.41    inference(resolution,[],[f44,f32])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f43])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    spl2_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f51])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(flattening,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    spl2_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    spl2_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f43])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl2_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    spl2_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f19,f35])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f30])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    v1_relat_1(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) & v1_relat_1(sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1)) => (k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) & v1_relat_1(sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.41    inference(negated_conjecture,[],[f6])).
% 0.21/0.41  fof(f6,conjecture,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ~spl2_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f25])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (29138)------------------------------
% 0.21/0.41  % (29138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (29138)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (29138)Memory used [KB]: 6140
% 0.21/0.41  % (29138)Time elapsed: 0.007 s
% 0.21/0.41  % (29138)------------------------------
% 0.21/0.41  % (29138)------------------------------
% 0.21/0.41  % (29127)Success in time 0.06 s
%------------------------------------------------------------------------------
