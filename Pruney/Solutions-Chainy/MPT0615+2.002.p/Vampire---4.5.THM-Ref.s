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
% DateTime   : Thu Dec  3 12:51:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 187 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f35,f72,f85])).

fof(f85,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f83,f29])).

fof(f29,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f83,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f80,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

fof(f80,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl2_2 ),
    inference(resolution,[],[f65,f32])).

fof(f32,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f61,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f20,f19])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f72,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f70,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f68,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f68,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f58,plain,
    ( ! [X8] :
        ( r1_tarski(sK0,X8)
        | ~ r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),X8) )
    | ~ spl2_2 ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,
    ( sK0 = k3_xboole_0(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ spl2_2 ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X0),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f25,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f35,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f17,f31,f27])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f16,f31,f27])).

fof(f16,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:12:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.41  % (13478)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (13479)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (13480)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (13473)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % (13473)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f34,f35,f72,f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ~spl2_1 | spl2_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    $false | (~spl2_1 | spl2_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f83,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    spl2_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ~r1_tarski(sK0,sK1) | spl2_2),
% 0.21/0.43    inference(subsumption_resolution,[],[f80,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | spl2_2),
% 0.21/0.43    inference(resolution,[],[f65,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl2_2 <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f61,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1) | ~v1_relat_1(sK0)) )),
% 0.21/0.43    inference(superposition,[],[f23,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.43    inference(resolution,[],[f20,f19])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl2_1 | ~spl2_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f70,f18])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ~v1_relat_1(sK1) | (spl2_1 | ~spl2_2)),
% 0.21/0.43    inference(resolution,[],[f68,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ~r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),sK1) | (spl2_1 | ~spl2_2)),
% 0.21/0.43    inference(resolution,[],[f58,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~r1_tarski(sK0,sK1) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X8] : (r1_tarski(sK0,X8) | ~r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),X8)) ) | ~spl2_2),
% 0.21/0.43    inference(superposition,[],[f48,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    sK0 = k3_xboole_0(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~spl2_2),
% 0.21/0.43    inference(resolution,[],[f24,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X2) | ~r1_tarski(X0,X2)) )),
% 0.21/0.43    inference(superposition,[],[f25,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~spl2_1 | ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f31,f27])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl2_1 | spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f31,f27])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (13473)------------------------------
% 0.21/0.43  % (13473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (13473)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (13473)Memory used [KB]: 10618
% 0.21/0.43  % (13473)Time elapsed: 0.006 s
% 0.21/0.43  % (13473)------------------------------
% 0.21/0.43  % (13473)------------------------------
% 0.21/0.43  % (13472)Success in time 0.076 s
%------------------------------------------------------------------------------
