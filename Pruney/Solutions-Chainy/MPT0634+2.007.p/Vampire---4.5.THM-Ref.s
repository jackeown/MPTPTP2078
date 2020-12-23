%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  73 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 155 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f35,f39,f50,f54,f59,f63])).

fof(f63,plain,
    ( ~ spl2_2
    | spl2_6
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl2_2
    | spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f49,f60])).

fof(f60,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f58,f29])).

fof(f29,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_8
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f49,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_6
  <=> k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f59,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f55,f52,f23,f57])).

fof(f23,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f52,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f55,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f53,f25])).

fof(f25,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f50,plain,
    ( ~ spl2_6
    | ~ spl2_1
    | spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f41,f37,f32,f23,f47])).

fof(f32,plain,
    ( spl2_3
  <=> k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f37,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f41,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) != k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f34,f40])).

fof(f40,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f38,f25])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f34,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f39,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f35,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f21,f32])).

fof(f21,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f19,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f19,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).

fof(f30,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f26,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (19089)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (19101)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (19093)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (19093)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f26,f30,f35,f39,f50,f54,f59,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ~spl2_2 | spl2_6 | ~spl2_8),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    $false | (~spl2_2 | spl2_6 | ~spl2_8)),
% 0.20/0.46    inference(subsumption_resolution,[],[f49,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) ) | (~spl2_2 | ~spl2_8)),
% 0.20/0.46    inference(superposition,[],[f58,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    spl2_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl2_8 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) != k1_relat_1(k7_relat_1(sK1,sK0)) | spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl2_6 <=> k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl2_8 | ~spl2_1 | ~spl2_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f55,f52,f23,f57])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl2_7 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_7)),
% 0.20/0.46    inference(resolution,[],[f53,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f23])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) ) | ~spl2_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f52])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    spl2_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f52])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f18,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ~spl2_6 | ~spl2_1 | spl2_3 | ~spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f41,f37,f32,f23,f47])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl2_3 <=> k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl2_4 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) != k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | spl2_3 | ~spl2_4)),
% 0.20/0.46    inference(backward_demodulation,[],[f34,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | (~spl2_1 | ~spl2_4)),
% 0.20/0.46    inference(resolution,[],[f38,f25])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) | spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f32])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ~spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f32])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 0.20/0.46    inference(backward_demodulation,[],[f19,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))),
% 0.20/0.46    inference(definition_unfolding,[],[f14,f16])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) & v1_relat_1(X1)) => (k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f15,f28])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f13,f23])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (19093)------------------------------
% 0.20/0.46  % (19093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (19093)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (19093)Memory used [KB]: 6140
% 0.20/0.46  % (19093)Time elapsed: 0.058 s
% 0.20/0.46  % (19093)------------------------------
% 0.20/0.46  % (19093)------------------------------
% 0.20/0.46  % (19085)Success in time 0.107 s
%------------------------------------------------------------------------------
