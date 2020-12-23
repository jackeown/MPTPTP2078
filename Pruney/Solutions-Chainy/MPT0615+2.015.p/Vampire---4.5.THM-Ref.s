%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  70 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 192 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f31,f40,f54,f98])).

fof(f98,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f96,f29])).

fof(f29,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl2_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f96,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f93,f16])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

fof(f93,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl2_2 ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f50,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f48,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f20,f35])).

fof(f35,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f18,f17])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f54,plain,
    ( ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1) ),
    inference(resolution,[],[f19,f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f51,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f39,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_3
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f40,plain,
    ( spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f36,f23,f38])).

fof(f36,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK0,X0) )
    | spl2_1 ),
    inference(resolution,[],[f21,f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f31,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f14,f26,f23])).

fof(f14,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f26,f23])).

fof(f15,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:09:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.43  % (31213)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.43  % (31219)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (31213)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f28,f31,f40,f54,f98])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    ~spl2_1 | spl2_2),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f97])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    $false | (~spl2_1 | spl2_2)),
% 0.22/0.43    inference(subsumption_resolution,[],[f96,f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    r1_tarski(sK0,sK1) | ~spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    spl2_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    ~r1_tarski(sK0,sK1) | spl2_2),
% 0.22/0.43    inference(subsumption_resolution,[],[f93,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    v1_relat_1(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | spl2_2),
% 0.22/0.43    inference(resolution,[],[f50,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    spl2_2 <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    ( ! [X1] : (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f48,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X1] : (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1) | ~v1_relat_1(sK0)) )),
% 0.22/0.43    inference(superposition,[],[f20,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.22/0.43    inference(resolution,[],[f18,f17])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ~spl2_2 | ~spl2_3),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f53])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    $false | (~spl2_2 | ~spl2_3)),
% 0.22/0.43    inference(subsumption_resolution,[],[f51,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) )),
% 0.22/0.43    inference(resolution,[],[f19,f16])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ~r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),sK1) | (~spl2_2 | ~spl2_3)),
% 0.22/0.43    inference(resolution,[],[f39,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f26])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK1)) ) | ~spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl2_3 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl2_3 | spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f36,f23,f38])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0)) ) | spl2_1),
% 0.22/0.43    inference(resolution,[],[f21,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ~r1_tarski(sK0,sK1) | spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f23])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl2_1 | spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f26,f23])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ~spl2_1 | ~spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f26,f23])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (31213)------------------------------
% 0.22/0.43  % (31213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (31213)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (31213)Memory used [KB]: 10618
% 0.22/0.43  % (31213)Time elapsed: 0.007 s
% 0.22/0.43  % (31213)------------------------------
% 0.22/0.43  % (31213)------------------------------
% 0.22/0.44  % (31214)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (31208)Success in time 0.067 s
%------------------------------------------------------------------------------
