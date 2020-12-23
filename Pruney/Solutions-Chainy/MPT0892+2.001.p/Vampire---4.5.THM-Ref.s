%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  62 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 156 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f45,f47,f52,f62])).

fof(f62,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl6_1
    | spl6_5 ),
    inference(subsumption_resolution,[],[f57,f18])).

fof(f18,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl6_1
  <=> r1_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f57,plain,
    ( ~ r1_xboole_0(sK0,sK3)
    | spl6_5 ),
    inference(resolution,[],[f44,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f44,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_5
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f52,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f38,f29,f24])).

fof(f24,plain,
    ( spl6_3
  <=> r1_xboole_0(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f29,plain,
    ( spl6_4
  <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK2,sK5)
    | spl6_4 ),
    inference(resolution,[],[f13,f31])).

fof(f31,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,
    ( ~ spl6_2
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f44,f36])).

fof(f36,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK4))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f22,f13])).

fof(f22,plain,
    ( r1_xboole_0(sK1,sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl6_2
  <=> r1_xboole_0(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f45,plain,
    ( ~ spl6_5
    | spl6_4 ),
    inference(avatar_split_clause,[],[f34,f29,f42])).

fof(f34,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f31,f12])).

fof(f32,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f9,f11,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f9,plain,(
    ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( r1_xboole_0(sK2,sK5)
      | r1_xboole_0(sK1,sK4)
      | r1_xboole_0(sK0,sK3) )
    & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( r1_xboole_0(X2,X5)
          | r1_xboole_0(X1,X4)
          | r1_xboole_0(X0,X3) )
        & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
   => ( ( r1_xboole_0(sK2,sK5)
        | r1_xboole_0(sK1,sK4)
        | r1_xboole_0(sK0,sK3) )
      & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( r1_xboole_0(X2,X5)
        | r1_xboole_0(X1,X4)
        | r1_xboole_0(X0,X3) )
      & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
       => ( ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_mcart_1)).

fof(f27,plain,
    ( spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f10,f24,f20,f16])).

fof(f10,plain,
    ( r1_xboole_0(sK2,sK5)
    | r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (28275)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (28275)Refutation not found, incomplete strategy% (28275)------------------------------
% 0.21/0.46  % (28275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (28275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (28275)Memory used [KB]: 10490
% 0.21/0.46  % (28275)Time elapsed: 0.054 s
% 0.21/0.46  % (28275)------------------------------
% 0.21/0.46  % (28275)------------------------------
% 0.21/0.47  % (28279)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (28279)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f27,f32,f45,f47,f52,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~spl6_1 | spl6_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    $false | (~spl6_1 | spl6_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK3) | ~spl6_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    spl6_1 <=> r1_xboole_0(sK0,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK3) | spl6_5),
% 0.21/0.47    inference(resolution,[],[f44,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl6_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl6_5 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ~spl6_3 | spl6_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f29,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    spl6_3 <=> r1_xboole_0(sK2,sK5)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    spl6_4 <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~r1_xboole_0(sK2,sK5) | spl6_4),
% 0.21/0.47    inference(resolution,[],[f13,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl6_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f29])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~spl6_2 | spl6_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    $false | (~spl6_2 | spl6_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f44,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK4))) ) | ~spl6_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f22,f13])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK4) | ~spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    spl6_2 <=> r1_xboole_0(sK1,sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~spl6_5 | spl6_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f29,f42])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl6_4),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f31,f12])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~spl6_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f29])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.47    inference(definition_unfolding,[],[f9,f11,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ~r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    (r1_xboole_0(sK2,sK5) | r1_xboole_0(sK1,sK4) | r1_xboole_0(sK0,sK3)) & ~r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5] : ((r1_xboole_0(X2,X5) | r1_xboole_0(X1,X4) | r1_xboole_0(X0,X3)) & ~r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) => ((r1_xboole_0(sK2,sK5) | r1_xboole_0(sK1,sK4) | r1_xboole_0(sK0,sK3)) & ~r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5] : ((r1_xboole_0(X2,X5) | r1_xboole_0(X1,X4) | r1_xboole_0(X0,X3)) & ~r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3,X4,X5] : (~r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) => (~r1_xboole_0(X2,X5) & ~r1_xboole_0(X1,X4) & ~r1_xboole_0(X0,X3)))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : (~r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) => (~r1_xboole_0(X2,X5) & ~r1_xboole_0(X1,X4) & ~r1_xboole_0(X0,X3)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_mcart_1)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    spl6_1 | spl6_2 | spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f24,f20,f16])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    r1_xboole_0(sK2,sK5) | r1_xboole_0(sK1,sK4) | r1_xboole_0(sK0,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (28279)------------------------------
% 0.21/0.47  % (28279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28279)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (28279)Memory used [KB]: 10618
% 0.21/0.47  % (28279)Time elapsed: 0.054 s
% 0.21/0.47  % (28279)------------------------------
% 0.21/0.47  % (28279)------------------------------
% 0.21/0.48  % (28263)Success in time 0.118 s
%------------------------------------------------------------------------------
