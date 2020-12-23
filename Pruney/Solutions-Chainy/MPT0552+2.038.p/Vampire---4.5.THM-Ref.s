%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 102 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  173 ( 264 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f51,f91,f103,f185,f196,f212])).

fof(f212,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | spl3_30 ),
    inference(subsumption_resolution,[],[f210,f28])).

fof(f28,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f210,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_4
    | spl3_30 ),
    inference(resolution,[],[f184,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f184,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_30
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f196,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | spl3_29 ),
    inference(subsumption_resolution,[],[f194,f28])).

fof(f194,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_4
    | spl3_29 ),
    inference(resolution,[],[f180,f36])).

fof(f180,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_29
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f185,plain,
    ( ~ spl3_29
    | ~ spl3_30
    | spl3_1
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f174,f101,f21,f182,f178])).

fof(f21,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f101,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
        | ~ v1_relat_1(k7_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f174,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_1
    | ~ spl3_17 ),
    inference(resolution,[],[f102,f23])).

fof(f23,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
        | ~ v1_relat_1(k7_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f99,f89,f49,f31,f101])).

fof(f31,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f89,plain,
    ( spl3_15
  <=> ! [X1,X0] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
        | ~ v1_relat_1(k7_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f98,f50])).

fof(f50,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
        | ~ v1_relat_1(k7_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f97,f50])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k9_relat_1(sK2,X1)))
        | ~ v1_relat_1(k7_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f96,f50])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X1))))
        | ~ v1_relat_1(k7_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(superposition,[],[f32,f90])).

fof(f90,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f89])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f91,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f86,f43,f26,f89])).

fof(f43,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f86,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f44,f28])).

fof(f44,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f51,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f46,f39,f26,f49])).

fof(f39,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f46,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(f41,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f24,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f21])).

fof(f15,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (17626)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.41  % (17619)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.41  % (17626)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f213,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f51,f91,f103,f185,f196,f212])).
% 0.21/0.41  fof(f212,plain,(
% 0.21/0.41    ~spl3_2 | ~spl3_4 | spl3_30),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.41  fof(f211,plain,(
% 0.21/0.41    $false | (~spl3_2 | ~spl3_4 | spl3_30)),
% 0.21/0.41    inference(subsumption_resolution,[],[f210,f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    spl3_2 <=> v1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f210,plain,(
% 0.21/0.41    ~v1_relat_1(sK2) | (~spl3_4 | spl3_30)),
% 0.21/0.41    inference(resolution,[],[f184,f36])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f184,plain,(
% 0.21/0.41    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_30),
% 0.21/0.41    inference(avatar_component_clause,[],[f182])).
% 0.21/0.41  fof(f182,plain,(
% 0.21/0.41    spl3_30 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.41  fof(f196,plain,(
% 0.21/0.41    ~spl3_2 | ~spl3_4 | spl3_29),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f195])).
% 0.21/0.41  fof(f195,plain,(
% 0.21/0.41    $false | (~spl3_2 | ~spl3_4 | spl3_29)),
% 0.21/0.41    inference(subsumption_resolution,[],[f194,f28])).
% 0.21/0.41  fof(f194,plain,(
% 0.21/0.41    ~v1_relat_1(sK2) | (~spl3_4 | spl3_29)),
% 0.21/0.41    inference(resolution,[],[f180,f36])).
% 0.21/0.41  fof(f180,plain,(
% 0.21/0.41    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_29),
% 0.21/0.41    inference(avatar_component_clause,[],[f178])).
% 0.21/0.41  fof(f178,plain,(
% 0.21/0.41    spl3_29 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.41  fof(f185,plain,(
% 0.21/0.41    ~spl3_29 | ~spl3_30 | spl3_1 | ~spl3_17),
% 0.21/0.41    inference(avatar_split_clause,[],[f174,f101,f21,f182,f178])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    spl3_17 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.41  fof(f174,plain,(
% 0.21/0.41    ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | (spl3_1 | ~spl3_17)),
% 0.21/0.41    inference(resolution,[],[f102,f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f21])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_17),
% 0.21/0.41    inference(avatar_component_clause,[],[f101])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    spl3_17 | ~spl3_3 | ~spl3_7 | ~spl3_15),
% 0.21/0.41    inference(avatar_split_clause,[],[f99,f89,f49,f31,f101])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    spl3_3 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    spl3_7 <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    spl3_15 <=> ! [X1,X0] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_3 | ~spl3_7 | ~spl3_15)),
% 0.21/0.41    inference(forward_demodulation,[],[f98,f50])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f49])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_3 | ~spl3_7 | ~spl3_15)),
% 0.21/0.41    inference(forward_demodulation,[],[f97,f50])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k9_relat_1(sK2,X1))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_3 | ~spl3_7 | ~spl3_15)),
% 0.21/0.41    inference(forward_demodulation,[],[f96,f50])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X1)))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_3 | ~spl3_15)),
% 0.21/0.41    inference(superposition,[],[f32,f90])).
% 0.21/0.41  fof(f90,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) ) | ~spl3_15),
% 0.21/0.41    inference(avatar_component_clause,[],[f89])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f31])).
% 0.21/0.41  fof(f91,plain,(
% 0.21/0.41    spl3_15 | ~spl3_2 | ~spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f86,f43,f26,f89])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl3_6 <=> ! [X1,X0,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) ) | (~spl3_2 | ~spl3_6)),
% 0.21/0.41    inference(resolution,[],[f44,f28])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) ) | ~spl3_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f43])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    spl3_7 | ~spl3_2 | ~spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f46,f39,f26,f49])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    spl3_5 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | (~spl3_2 | ~spl3_5)),
% 0.21/0.41    inference(resolution,[],[f40,f28])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f39])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f19,f43])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f39])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    spl3_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f16,f31])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    v1_relat_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.41    inference(negated_conjecture,[],[f5])).
% 0.21/0.41  fof(f5,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ~spl3_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f15,f21])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (17626)------------------------------
% 0.21/0.41  % (17626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (17626)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (17626)Memory used [KB]: 6268
% 0.21/0.41  % (17626)Time elapsed: 0.032 s
% 0.21/0.41  % (17626)------------------------------
% 0.21/0.41  % (17626)------------------------------
% 0.21/0.42  % (17610)Success in time 0.061 s
%------------------------------------------------------------------------------
