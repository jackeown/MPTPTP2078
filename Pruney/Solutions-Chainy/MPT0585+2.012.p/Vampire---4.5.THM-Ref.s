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
% DateTime   : Thu Dec  3 12:50:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 164 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f48,f80,f100,f164,f203])).

fof(f203,plain,
    ( spl2_9
    | ~ spl2_21 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl2_9
    | ~ spl2_21 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(sK1))
    | spl2_9
    | ~ spl2_21 ),
    inference(superposition,[],[f79,f152])).

fof(f152,plain,
    ( ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k3_xboole_0(X1,k1_relat_1(sK0)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl2_21
  <=> ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k3_xboole_0(X1,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f79,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_9
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f164,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f163,f98,f24,f151])).

fof(f24,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f98,plain,
    ( spl2_13
  <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f163,plain,
    ( ! [X4] : k7_relat_1(sK0,X4) = k7_relat_1(sK0,k3_xboole_0(X4,k1_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f148,f26])).

fof(f26,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f148,plain,
    ( ! [X4] :
        ( k7_relat_1(sK0,X4) = k7_relat_1(sK0,k3_xboole_0(X4,k1_relat_1(sK0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl2_13 ),
    inference(superposition,[],[f22,f99])).

fof(f99,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f100,plain,
    ( spl2_13
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f94,f24,f98])).

fof(f94,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(sK0))
    | ~ spl2_1 ),
    inference(resolution,[],[f50,f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f49,f18])).

fof(f18,plain,(
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

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f80,plain,
    ( ~ spl2_9
    | spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f72,f46,f29,f77])).

fof(f29,plain,
    ( spl2_2
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f46,plain,
    ( spl2_5
  <=> ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f72,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
    | spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f31,f47])).

fof(f47,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f31,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f48,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f39,f34,f46])).

fof(f34,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f39,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1)
    | ~ spl2_3 ),
    inference(resolution,[],[f20,f36])).

fof(f36,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f37,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f32,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f17,f24])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:23:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (9407)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (9403)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.44  % (9402)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.44  % (9402)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f204,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f27,f32,f37,f48,f80,f100,f164,f203])).
% 0.22/0.44  fof(f203,plain,(
% 0.22/0.44    spl2_9 | ~spl2_21),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f202])).
% 0.22/0.44  fof(f202,plain,(
% 0.22/0.44    $false | (spl2_9 | ~spl2_21)),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f201])).
% 0.22/0.44  fof(f201,plain,(
% 0.22/0.44    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(sK1)) | (spl2_9 | ~spl2_21)),
% 0.22/0.44    inference(superposition,[],[f79,f152])).
% 0.22/0.44  fof(f152,plain,(
% 0.22/0.44    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK0,k3_xboole_0(X1,k1_relat_1(sK0)))) ) | ~spl2_21),
% 0.22/0.44    inference(avatar_component_clause,[],[f151])).
% 0.22/0.44  fof(f151,plain,(
% 0.22/0.44    spl2_21 <=> ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k3_xboole_0(X1,k1_relat_1(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) | spl2_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f77])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    spl2_9 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.44  fof(f164,plain,(
% 0.22/0.44    spl2_21 | ~spl2_1 | ~spl2_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f163,f98,f24,f151])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    spl2_1 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    spl2_13 <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    ( ! [X4] : (k7_relat_1(sK0,X4) = k7_relat_1(sK0,k3_xboole_0(X4,k1_relat_1(sK0)))) ) | (~spl2_1 | ~spl2_13)),
% 0.22/0.44    inference(subsumption_resolution,[],[f148,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f24])).
% 0.22/0.44  fof(f148,plain,(
% 0.22/0.44    ( ! [X4] : (k7_relat_1(sK0,X4) = k7_relat_1(sK0,k3_xboole_0(X4,k1_relat_1(sK0))) | ~v1_relat_1(sK0)) ) | ~spl2_13),
% 0.22/0.44    inference(superposition,[],[f22,f99])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(sK0))) ) | ~spl2_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f98])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    spl2_13 | ~spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f94,f24,f98])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(sK0))) ) | ~spl2_1),
% 0.22/0.44    inference(resolution,[],[f50,f26])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0))) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f49,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(resolution,[],[f21,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    ~spl2_9 | spl2_2 | ~spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f72,f46,f29,f77])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl2_2 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl2_5 <=> ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) | (spl2_2 | ~spl2_5)),
% 0.22/0.45    inference(superposition,[],[f31,f47])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1)) ) | ~spl2_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f46])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f29])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    spl2_5 | ~spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f39,f34,f46])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    spl2_3 <=> v1_relat_1(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1)) ) | ~spl2_3),
% 0.22/0.45    inference(resolution,[],[f20,f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    v1_relat_1(sK1) | ~spl2_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f34])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f15,f34])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ~spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f16,f29])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f17,f24])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (9402)------------------------------
% 0.22/0.45  % (9402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (9402)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (9402)Memory used [KB]: 10618
% 0.22/0.45  % (9402)Time elapsed: 0.038 s
% 0.22/0.45  % (9402)------------------------------
% 0.22/0.45  % (9402)------------------------------
% 0.22/0.45  % (9400)Success in time 0.088 s
%------------------------------------------------------------------------------
