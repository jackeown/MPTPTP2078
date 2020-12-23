%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 119 expanded)
%              Number of leaves         :    7 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  166 ( 309 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13111)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f47,f48,f49,f108,f142,f152,f203])).

% (13099)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f203,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f201,f153])).

fof(f153,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(sK2,X0))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f45,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f201,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f187,f147])).

fof(f147,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(sK1,X0))
    | spl5_2 ),
    inference(resolution,[],[f41,f33])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f187,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f37,plain,
    ( r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f152,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f144,f91])).

fof(f91,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | spl5_1 ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f144,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f44,f41,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f142,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f140,f50])).

fof(f50,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

% (13111)Refutation not found, incomplete strategy% (13111)------------------------------
% (13111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f140,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f124,f109])).

% (13111)Termination reason: Refutation not found, incomplete strategy

% (13111)Memory used [KB]: 1663
% (13111)Time elapsed: 0.109 s
% (13111)------------------------------
% (13111)------------------------------
fof(f109,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK2))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f44,f32])).

fof(f124,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f30])).

fof(f108,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f90,f58])).

fof(f58,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f40,f45,f31])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | spl5_1 ),
    inference(resolution,[],[f36,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f27,f43,f39,f35])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f7,f11])).

% (13099)Refutation not found, incomplete strategy% (13099)------------------------------
% (13099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f11,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f7,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <~> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
      <=> ~ ( r2_hidden(X0,X1)
          <=> r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f48,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f26,f43,f39,f35])).

fof(f26,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f8,f11])).

fof(f8,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,
    ( spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f25,f43,f39,f35])).

fof(f25,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f9,f11])).

fof(f9,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f24,f43,f39,f35])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f10,f11])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (13098)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (13090)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (13114)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (13093)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (13094)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (13089)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (13098)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (13106)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (13105)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (13101)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  % (13111)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f46,f47,f48,f49,f108,f142,f152,f203])).
% 0.20/0.52  % (13099)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    ~spl5_1 | spl5_2 | spl5_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    $false | (~spl5_1 | spl5_2 | spl5_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f201,f153])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(sK2,X0))) ) | spl5_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK2) | spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl5_3 <=> r2_hidden(sK0,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(sK2,sK1)) | (~spl5_1 | spl5_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f187,f147])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(sK1,X0))) ) | spl5_2),
% 0.20/0.52    inference(resolution,[],[f41,f33])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK1) | spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    spl5_2 <=> r2_hidden(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(sK1,sK2)) | r2_hidden(sK0,k4_xboole_0(sK2,sK1)) | ~spl5_1),
% 0.20/0.52    inference(resolution,[],[f37,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    spl5_1 <=> r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    spl5_1 | spl5_2 | ~spl5_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    $false | (spl5_1 | spl5_2 | ~spl5_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f144,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k4_xboole_0(sK2,sK1)) | spl5_1),
% 0.20/0.52    inference(resolution,[],[f36,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f35])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(sK2,sK1)) | (spl5_2 | ~spl5_3)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f44,f41,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    r2_hidden(sK0,sK2) | ~spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f140,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1))) ) | ~spl5_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f40,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    r2_hidden(sK0,sK1) | ~spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f39])).
% 0.20/0.52  % (13111)Refutation not found, incomplete strategy% (13111)------------------------------
% 0.20/0.52  % (13111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(sK2,sK1)) | (~spl5_1 | ~spl5_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f124,f109])).
% 0.20/0.52  % (13111)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13111)Memory used [KB]: 1663
% 0.20/0.52  % (13111)Time elapsed: 0.109 s
% 0.20/0.52  % (13111)------------------------------
% 0.20/0.52  % (13111)------------------------------
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK2))) ) | ~spl5_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f44,f32])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(sK1,sK2)) | r2_hidden(sK0,k4_xboole_0(sK2,sK1)) | ~spl5_1),
% 0.20/0.52    inference(resolution,[],[f37,f30])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl5_1 | ~spl5_2 | spl5_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    $false | (spl5_1 | ~spl5_2 | spl5_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f90,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(sK1,sK2)) | (~spl5_2 | spl5_3)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f40,f45,f31])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k4_xboole_0(sK1,sK2)) | spl5_1),
% 0.20/0.52    inference(resolution,[],[f36,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ~spl5_1 | spl5_2 | ~spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f43,f39,f35])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK2) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))),
% 0.20/0.52    inference(definition_unfolding,[],[f7,f11])).
% 0.20/0.52  % (13099)Refutation not found, incomplete strategy% (13099)------------------------------
% 0.20/0.52  % (13099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK2) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <~> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.52    inference(negated_conjecture,[],[f4])).
% 0.20/0.52  fof(f4,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ~spl5_1 | ~spl5_2 | spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f43,f39,f35])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))),
% 0.20/0.52    inference(definition_unfolding,[],[f8,f11])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl5_1 | spl5_2 | spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f43,f39,f35])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    r2_hidden(sK0,sK2) | r2_hidden(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))),
% 0.20/0.52    inference(definition_unfolding,[],[f9,f11])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    r2_hidden(sK0,sK2) | r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    spl5_1 | ~spl5_2 | ~spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f24,f43,f39,f35])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))),
% 0.20/0.52    inference(definition_unfolding,[],[f10,f11])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (13098)------------------------------
% 0.20/0.52  % (13098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13098)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (13098)Memory used [KB]: 10746
% 0.20/0.52  % (13098)Time elapsed: 0.099 s
% 0.20/0.52  % (13098)------------------------------
% 0.20/0.52  % (13098)------------------------------
% 0.20/0.52  % (13097)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (13091)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (13112)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (13092)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (13088)Success in time 0.169 s
%------------------------------------------------------------------------------
