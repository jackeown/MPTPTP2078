%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  66 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 147 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f43,f56,f114,f148,f283])).

fof(f283,plain,
    ( spl3_4
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl3_4
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f277,f42])).

fof(f42,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f277,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(resolution,[],[f147,f112])).

fof(f112,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_16
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,sK2))
        | k1_xboole_0 = k3_xboole_0(sK0,X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,sK2))
        | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f148,plain,
    ( spl3_20
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f143,f22,f146])).

fof(f22,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,sK2))
        | k1_xboole_0 = k3_xboole_0(sK0,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f58,f24])).

fof(f24,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f58,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(k3_xboole_0(X1,X2),X3)
      | k1_xboole_0 = k3_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f20,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f114,plain,
    ( spl3_16
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f91,f54,f111])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f91,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(sK0,X1),k3_xboole_0(X1,sK2))
    | ~ spl3_6 ),
    inference(superposition,[],[f55,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK2,X0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f27,f54])).

fof(f27,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK2,X0))
    | ~ spl3_2 ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f43,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f38,f32,f40])).

fof(f32,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f38,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(resolution,[],[f17,f34])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f35,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f12,f32])).

fof(f12,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f22])).

fof(f14,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (9790)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (9791)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (9789)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (9785)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (9786)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (9793)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (9786)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f289,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f25,f30,f35,f43,f56,f114,f148,f283])).
% 0.21/0.43  fof(f283,plain,(
% 0.21/0.43    spl3_4 | ~spl3_16 | ~spl3_20),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f282])).
% 0.21/0.43  fof(f282,plain,(
% 0.21/0.43    $false | (spl3_4 | ~spl3_16 | ~spl3_20)),
% 0.21/0.43    inference(subsumption_resolution,[],[f277,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl3_4 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f277,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_16 | ~spl3_20)),
% 0.21/0.43    inference(resolution,[],[f147,f112])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK2))) ) | ~spl3_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f111])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    spl3_16 <=> ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.43  fof(f147,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK0,X0)) ) | ~spl3_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f146])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    spl3_20 <=> ! [X0] : (~r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK0,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.43  fof(f148,plain,(
% 0.21/0.43    spl3_20 | ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f143,f22,f146])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    spl3_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f143,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK0,X0)) ) | ~spl3_1),
% 0.21/0.43    inference(resolution,[],[f58,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f22])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (~r1_xboole_0(X1,X3) | ~r1_tarski(k3_xboole_0(X1,X2),X3) | k1_xboole_0 = k3_xboole_0(X1,X2)) )),
% 0.21/0.43    inference(resolution,[],[f20,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    spl3_16 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f91,f54,f111])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_6 <=> ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK2,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(k3_xboole_0(sK0,X1),k3_xboole_0(X1,sK2))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f55,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK2,X0))) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl3_6 | ~spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f51,f27,f54])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK2,X0))) ) | ~spl3_2),
% 0.21/0.43    inference(resolution,[],[f19,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ~spl3_4 | spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f38,f32,f40])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl3_3),
% 0.21/0.43    inference(resolution,[],[f17,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f12,f32])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f27])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    r1_tarski(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f14,f22])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (9786)------------------------------
% 0.21/0.43  % (9786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (9786)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (9786)Memory used [KB]: 10746
% 0.21/0.43  % (9786)Time elapsed: 0.010 s
% 0.21/0.43  % (9786)------------------------------
% 0.21/0.43  % (9786)------------------------------
% 0.21/0.43  % (9784)Success in time 0.081 s
%------------------------------------------------------------------------------
