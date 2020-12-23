%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  98 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 ( 327 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f37,f45,f50,f55,f67,f71,f75,f82,f116,f126,f132])).

fof(f132,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(avatar_contradiction_clause,[],[f131])).

% (3070)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f131,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f130,f29])).

fof(f29,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl10_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f130,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f129,f33])).

fof(f33,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl10_2
  <=> r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f129,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(resolution,[],[f125,f66])).

fof(f66,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_10
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,X0,sK0),sK1)
        | ~ r2_hidden(sK0,k10_relat_1(sK2,X0)) )
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_21
  <=> ! [X0] :
        ( ~ r2_hidden(sK0,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK5(sK2,X0,sK0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f126,plain,
    ( spl10_21
    | ~ spl10_7
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f118,f114,f53,f124])).

fof(f53,plain,
    ( spl10_7
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f114,plain,
    ( spl10_19
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2)
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK5(sK2,X0,sK0),sK1) )
    | ~ spl10_7
    | ~ spl10_19 ),
    inference(resolution,[],[f115,f54])).

fof(f54,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK0,X3),sK2)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2)
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) )
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl10_19
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f88,f73,f28,f114])).

fof(f73,plain,
    ( spl10_12
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2)
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) )
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(resolution,[],[f74,f29])).

fof(f74,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f73])).

fof(f82,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f29,f36,f46,f44,f70])).

fof(f70,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl10_11
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK0,sK3),sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl10_5
  <=> r2_hidden(k4_tarski(sK0,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f36,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl10_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f75,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f71,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f22,f69])).

fof(f22,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f23,f65])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f55,plain,
    ( spl10_7
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f51,f48,f53])).

fof(f48,plain,
    ( spl10_6
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f51,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) )
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f49,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( ~ spl10_2
    | spl10_6 ),
    inference(avatar_split_clause,[],[f7,f48,f32])).

fof(f7,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(sK0,X3),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(sK0,k10_relat_1(sK2,sK1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k10_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f45,plain,
    ( spl10_2
    | spl10_5 ),
    inference(avatar_split_clause,[],[f9,f43,f32])).

fof(f9,plain,
    ( r2_hidden(k4_tarski(sK0,sK3),sK2)
    | r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,
    ( spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f10,f35,f32])).

fof(f10,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f30,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (3079)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (3078)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (3079)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (3080)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (3072)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f30,f37,f45,f50,f55,f67,f71,f75,f82,f116,f126,f132])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~spl10_1 | ~spl10_2 | ~spl10_10 | ~spl10_21),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f131])).
% 0.20/0.48  % (3070)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    $false | (~spl10_1 | ~spl10_2 | ~spl10_10 | ~spl10_21)),
% 0.20/0.48    inference(subsumption_resolution,[],[f130,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v1_relat_1(sK2) | ~spl10_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    spl10_1 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | (~spl10_2 | ~spl10_10 | ~spl10_21)),
% 0.20/0.48    inference(subsumption_resolution,[],[f129,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    r2_hidden(sK0,k10_relat_1(sK2,sK1)) | ~spl10_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    spl10_2 <=> r2_hidden(sK0,k10_relat_1(sK2,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k10_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl10_10 | ~spl10_21)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k10_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,k10_relat_1(sK2,sK1)) | (~spl10_10 | ~spl10_21)),
% 0.20/0.48    inference(resolution,[],[f125,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~v1_relat_1(X0) | ~r2_hidden(X3,k10_relat_1(X0,X1))) ) | ~spl10_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl10_10 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK5(sK2,X0,sK0),sK1) | ~r2_hidden(sK0,k10_relat_1(sK2,X0))) ) | ~spl10_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    spl10_21 <=> ! [X0] : (~r2_hidden(sK0,k10_relat_1(sK2,X0)) | ~r2_hidden(sK5(sK2,X0,sK0),sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl10_21 | ~spl10_7 | ~spl10_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f118,f114,f53,f124])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl10_7 <=> ! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(k4_tarski(sK0,X3),sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl10_19 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2) | ~r2_hidden(X0,k10_relat_1(sK2,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK0,k10_relat_1(sK2,X0)) | ~r2_hidden(sK5(sK2,X0,sK0),sK1)) ) | (~spl10_7 | ~spl10_19)),
% 0.20/0.48    inference(resolution,[],[f115,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(k4_tarski(sK0,X3),sK2) | ~r2_hidden(X3,sK1)) ) | ~spl10_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2) | ~r2_hidden(X0,k10_relat_1(sK2,X1))) ) | ~spl10_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f114])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    spl10_19 | ~spl10_1 | ~spl10_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f88,f73,f28,f114])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl10_12 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0) | ~r2_hidden(X3,k10_relat_1(X0,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2) | ~r2_hidden(X0,k10_relat_1(sK2,X1))) ) | (~spl10_1 | ~spl10_12)),
% 0.20/0.48    inference(resolution,[],[f74,f29])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0) | ~r2_hidden(X3,k10_relat_1(X0,X1))) ) | ~spl10_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f73])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_5 | ~spl10_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    $false | (~spl10_1 | spl10_2 | ~spl10_3 | ~spl10_5 | ~spl10_11)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f29,f36,f46,f44,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1))) ) | ~spl10_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl10_11 <=> ! [X1,X3,X0,X4] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK3),sK2) | ~spl10_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl10_5 <=> r2_hidden(k4_tarski(sK0,sK3),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k10_relat_1(sK2,sK1)) | spl10_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f32])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    r2_hidden(sK3,sK1) | ~spl10_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    spl10_3 <=> r2_hidden(sK3,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl10_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f73])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl10_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f69])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl10_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f65])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl10_7 | ~spl10_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f51,f48,f53])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl10_6 <=> ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~r2_hidden(X3,sK1) | ~r2_hidden(k4_tarski(sK0,X3),sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(k4_tarski(sK0,X3),sK2)) ) | ~spl10_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f49,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~r2_hidden(X3,sK1) | ~r2_hidden(k4_tarski(sK0,X3),sK2)) ) | ~spl10_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ~spl10_2 | spl10_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f7,f48,f32])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~r2_hidden(k4_tarski(sK0,X3),sK2) | ~r2_hidden(X3,sK1) | ~r2_hidden(sK0,k10_relat_1(sK2,sK1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <~> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl10_2 | spl10_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f9,f43,f32])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK3),sK2) | r2_hidden(sK0,k10_relat_1(sK2,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl10_2 | spl10_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f10,f35,f32])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    r2_hidden(sK3,sK1) | r2_hidden(sK0,k10_relat_1(sK2,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    spl10_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f11,f28])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (3079)------------------------------
% 0.20/0.48  % (3079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3079)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (3079)Memory used [KB]: 10618
% 0.20/0.48  % (3079)Time elapsed: 0.056 s
% 0.20/0.48  % (3079)------------------------------
% 0.20/0.48  % (3079)------------------------------
% 0.20/0.48  % (3088)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (3069)Success in time 0.125 s
%------------------------------------------------------------------------------
