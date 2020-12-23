%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  65 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 154 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f45,f67])).

fof(f67,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f29,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f64,f26])).

fof(f26,plain,
    ( v3_ordinal1(sK1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> v3_ordinal1(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( ~ v3_ordinal1(sK1(sK0))
    | v3_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f63,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | ~ v3_ordinal1(sK1(X0))
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ? [X1] :
          ( ( ~ r1_tarski(X1,X0)
            | ~ v3_ordinal1(X1) )
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f63,plain,
    ( r1_tarski(sK1(sK0),sK0)
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( r1_tarski(sK1(sK0),sK0)
    | r1_tarski(sK1(sK0),sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f57,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f57,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1(sK0),X2),sK0)
        | r1_tarski(sK1(sK0),X2) )
    | ~ spl3_1 ),
    inference(resolution,[],[f55,f13])).

fof(f13,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f55,plain,
    ( ! [X2] :
        ( v3_ordinal1(sK2(sK1(sK0),X2))
        | r1_tarski(sK1(sK0),X2) )
    | ~ spl3_1 ),
    inference(resolution,[],[f39,f26])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_tarski(X1,X2)
      | v3_ordinal1(sK2(X1,X2)) ) ),
    inference(resolution,[],[f19,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | ~ spl3_2 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f21,f32])).

fof(f32,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f30,f13])).

fof(f30,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f43,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f20,f19])).

fof(f31,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f22,f28,f24])).

fof(f22,plain,
    ( v3_ordinal1(sK0)
    | v3_ordinal1(sK1(sK0)) ),
    inference(resolution,[],[f16,f14])).

fof(f14,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (29577)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.46  % (29579)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (29579)Refutation not found, incomplete strategy% (29579)------------------------------
% 0.21/0.47  % (29579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (29579)Memory used [KB]: 5373
% 0.21/0.47  % (29579)Time elapsed: 0.005 s
% 0.21/0.47  % (29579)------------------------------
% 0.21/0.47  % (29579)------------------------------
% 0.21/0.47  % (29571)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (29585)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.47  % (29581)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.47  % (29571)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f31,f45,f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ~spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~v3_ordinal1(sK0) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    spl3_2 <=> v3_ordinal1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    v3_ordinal1(sK0) | ~spl3_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v3_ordinal1(sK1(sK0)) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    spl3_1 <=> v3_ordinal1(sK1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~v3_ordinal1(sK1(sK0)) | v3_ordinal1(sK0) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f63,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(sK1(X0),X0) | ~v3_ordinal1(sK1(X0)) | v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) | ? [X1] : ((~r1_tarski(X1,X0) | ~v3_ordinal1(X1)) & r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    r1_tarski(sK1(sK0),sK0) | ~spl3_1),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    r1_tarski(sK1(sK0),sK0) | r1_tarski(sK1(sK0),sK0) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f57,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X2] : (r2_hidden(sK2(sK1(sK0),X2),sK0) | r1_tarski(sK1(sK0),X2)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f55,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(X1,sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : ! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X2] : (v3_ordinal1(sK2(sK1(sK0),X2)) | r1_tarski(sK1(sK0),X2)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f39,f26])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v3_ordinal1(X1) | r1_tarski(X1,X2) | v3_ordinal1(sK2(X1,X2))) )),
% 0.21/0.47    inference(resolution,[],[f19,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    $false | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f43,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK0) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f21,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    r2_hidden(sK0,sK0) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f30,f13])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v3_ordinal1(sK0) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f28])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f20,f19])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f28,f24])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v3_ordinal1(sK0) | v3_ordinal1(sK1(sK0))),
% 0.21/0.47    inference(resolution,[],[f16,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (29571)------------------------------
% 0.21/0.47  % (29571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29571)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (29571)Memory used [KB]: 5373
% 0.21/0.47  % (29571)Time elapsed: 0.005 s
% 0.21/0.47  % (29571)------------------------------
% 0.21/0.47  % (29571)------------------------------
% 0.21/0.47  % (29564)Success in time 0.118 s
%------------------------------------------------------------------------------
