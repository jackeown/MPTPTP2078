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
% DateTime   : Thu Dec  3 12:51:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 115 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 243 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f39,f40,f56,f99,f113,f123,f125])).

fof(f125,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl5_8 ),
    inference(resolution,[],[f122,f41])).

fof(f41,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f23,f14])).

fof(f14,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f15])).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f122,plain,
    ( r2_hidden(sK3(sK1,sK0),k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_8
  <=> r2_hidden(sK3(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f123,plain,
    ( ~ spl5_1
    | spl5_8
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f118,f110,f36,f120,f27])).

fof(f27,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f36,plain,
    ( spl5_3
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f110,plain,
    ( spl5_7
  <=> r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f118,plain,
    ( r2_hidden(sK3(sK1,sK0),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f116,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f116,plain,
    ( r2_hidden(sK3(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f112,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f112,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f108,f32,f110])).

fof(f32,plain,
    ( spl5_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f108,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f33,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f99,plain,
    ( spl5_3
    | ~ spl5_1
    | spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f94,f53,f32,f27,f36])).

fof(f53,plain,
    ( spl5_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f94,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f92,f34])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f92,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_relat_1(sK1))
        | k1_xboole_0 = k11_relat_1(sK1,X1) )
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(resolution,[],[f89,f25])).

fof(f25,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,k11_relat_1(sK1,X0))),sK1)
        | k1_xboole_0 = k11_relat_1(sK1,X0) )
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f29])).

fof(f29,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f67,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k11_relat_1(X1,X2)
        | r2_hidden(k4_tarski(X2,sK2(k1_xboole_0,k11_relat_1(X1,X2))),X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f62,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,
    ( ! [X6] :
        ( r2_hidden(sK2(k1_xboole_0,X6),X6)
        | k1_xboole_0 = X6 )
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f45,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f45,plain,(
    ! [X6] :
      ( r2_hidden(sK2(k1_xboole_0,X6),X6)
      | k1_relat_1(k1_xboole_0) = X6 ) ),
    inference(resolution,[],[f18,f41])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f49,f53])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f45,f41])).

fof(f40,plain,
    ( spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f11,f36,f32])).

fof(f11,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f39,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f12,f36,f32])).

fof(f12,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:05:44 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (8188)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.49  % (8182)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.49  % (8192)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.49  % (8188)Refutation not found, incomplete strategy% (8188)------------------------------
% 0.23/0.49  % (8188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (8188)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (8188)Memory used [KB]: 10618
% 0.23/0.49  % (8188)Time elapsed: 0.077 s
% 0.23/0.49  % (8188)------------------------------
% 0.23/0.49  % (8188)------------------------------
% 0.23/0.49  % (8200)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.49  % (8208)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.49  % (8182)Refutation not found, incomplete strategy% (8182)------------------------------
% 0.23/0.49  % (8182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (8182)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (8182)Memory used [KB]: 10618
% 0.23/0.49  % (8182)Time elapsed: 0.076 s
% 0.23/0.49  % (8182)------------------------------
% 0.23/0.49  % (8182)------------------------------
% 0.23/0.50  % (8196)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.50  % (8196)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f126,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f30,f39,f40,f56,f99,f113,f123,f125])).
% 0.23/0.50  fof(f125,plain,(
% 0.23/0.50    ~spl5_8),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f124])).
% 0.23/0.50  fof(f124,plain,(
% 0.23/0.50    $false | ~spl5_8),
% 0.23/0.50    inference(resolution,[],[f122,f41])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.50    inference(resolution,[],[f23,f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.50    inference(definition_unfolding,[],[f20,f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,plain,(
% 0.23/0.50    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.23/0.50  fof(f122,plain,(
% 0.23/0.50    r2_hidden(sK3(sK1,sK0),k1_xboole_0) | ~spl5_8),
% 0.23/0.50    inference(avatar_component_clause,[],[f120])).
% 0.23/0.50  fof(f120,plain,(
% 0.23/0.50    spl5_8 <=> r2_hidden(sK3(sK1,sK0),k1_xboole_0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.23/0.50  fof(f123,plain,(
% 0.23/0.50    ~spl5_1 | spl5_8 | ~spl5_3 | ~spl5_7),
% 0.23/0.50    inference(avatar_split_clause,[],[f118,f110,f36,f120,f27])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    spl5_1 <=> v1_relat_1(sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.50  fof(f36,plain,(
% 0.23/0.50    spl5_3 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.23/0.50  fof(f110,plain,(
% 0.23/0.50    spl5_7 <=> r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.23/0.50  fof(f118,plain,(
% 0.23/0.50    r2_hidden(sK3(sK1,sK0),k1_xboole_0) | ~v1_relat_1(sK1) | (~spl5_3 | ~spl5_7)),
% 0.23/0.50    inference(forward_demodulation,[],[f116,f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl5_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f36])).
% 0.23/0.50  fof(f116,plain,(
% 0.23/0.50    r2_hidden(sK3(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl5_7),
% 0.23/0.50    inference(resolution,[],[f112,f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.23/0.50  fof(f112,plain,(
% 0.23/0.50    r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1) | ~spl5_7),
% 0.23/0.50    inference(avatar_component_clause,[],[f110])).
% 0.23/0.50  fof(f113,plain,(
% 0.23/0.50    spl5_7 | ~spl5_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f108,f32,f110])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    spl5_2 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.23/0.50  fof(f108,plain,(
% 0.23/0.50    r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1) | ~spl5_2),
% 0.23/0.50    inference(resolution,[],[f33,f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)) )),
% 0.23/0.50    inference(equality_resolution,[],[f17])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl5_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f32])).
% 0.23/0.50  fof(f99,plain,(
% 0.23/0.50    spl5_3 | ~spl5_1 | spl5_2 | ~spl5_4),
% 0.23/0.50    inference(avatar_split_clause,[],[f94,f53,f32,f27,f36])).
% 0.23/0.50  fof(f53,plain,(
% 0.23/0.50    spl5_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.23/0.50  fof(f94,plain,(
% 0.23/0.50    k1_xboole_0 = k11_relat_1(sK1,sK0) | (~spl5_1 | spl5_2 | ~spl5_4)),
% 0.23/0.50    inference(resolution,[],[f92,f34])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl5_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f32])).
% 0.23/0.50  fof(f92,plain,(
% 0.23/0.50    ( ! [X1] : (r2_hidden(X1,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X1)) ) | (~spl5_1 | ~spl5_4)),
% 0.23/0.50    inference(resolution,[],[f89,f25])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.23/0.50    inference(equality_resolution,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f89,plain,(
% 0.23/0.50    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,k11_relat_1(sK1,X0))),sK1) | k1_xboole_0 = k11_relat_1(sK1,X0)) ) | (~spl5_1 | ~spl5_4)),
% 0.23/0.50    inference(resolution,[],[f67,f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    v1_relat_1(sK1) | ~spl5_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f27])).
% 0.23/0.50  fof(f67,plain,(
% 0.23/0.50    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X2) | r2_hidden(k4_tarski(X2,sK2(k1_xboole_0,k11_relat_1(X1,X2))),X1)) ) | ~spl5_4),
% 0.23/0.50    inference(resolution,[],[f62,f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f62,plain,(
% 0.23/0.50    ( ! [X6] : (r2_hidden(sK2(k1_xboole_0,X6),X6) | k1_xboole_0 = X6) ) | ~spl5_4),
% 0.23/0.50    inference(backward_demodulation,[],[f45,f55])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_4),
% 0.23/0.50    inference(avatar_component_clause,[],[f53])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    ( ! [X6] : (r2_hidden(sK2(k1_xboole_0,X6),X6) | k1_relat_1(k1_xboole_0) = X6) )),
% 0.23/0.50    inference(resolution,[],[f18,f41])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f56,plain,(
% 0.23/0.50    spl5_4),
% 0.23/0.50    inference(avatar_split_clause,[],[f49,f53])).
% 0.23/0.50  fof(f49,plain,(
% 0.23/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.50    inference(resolution,[],[f45,f41])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    spl5_2 | ~spl5_3),
% 0.23/0.50    inference(avatar_split_clause,[],[f11,f36,f32])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.23/0.50    inference(cnf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,plain,(
% 0.23/0.50    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.23/0.50    inference(negated_conjecture,[],[f6])).
% 0.23/0.50  fof(f6,conjecture,(
% 0.23/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ~spl5_2 | spl5_3),
% 0.23/0.50    inference(avatar_split_clause,[],[f12,f36,f32])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.23/0.50    inference(cnf_transformation,[],[f8])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    spl5_1),
% 0.23/0.50    inference(avatar_split_clause,[],[f13,f27])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    v1_relat_1(sK1)),
% 0.23/0.50    inference(cnf_transformation,[],[f8])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (8196)------------------------------
% 0.23/0.50  % (8196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (8196)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (8196)Memory used [KB]: 10746
% 0.23/0.50  % (8196)Time elapsed: 0.094 s
% 0.23/0.50  % (8196)------------------------------
% 0.23/0.50  % (8196)------------------------------
% 0.23/0.50  % (8179)Success in time 0.125 s
%------------------------------------------------------------------------------
