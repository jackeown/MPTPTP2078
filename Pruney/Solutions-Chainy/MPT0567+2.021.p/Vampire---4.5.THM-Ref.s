%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 196 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f454,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f63,f83,f451])).

fof(f451,plain,
    ( ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f449,f95])).

fof(f95,plain,
    ( ! [X0,X1] : sP1(X0,sK2,X1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f10,f12,f11])).

fof(f11,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X0,X3),X2)
          & r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f54,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f449,plain,
    ( ~ sP1(sK3(k10_relat_1(sK2,k1_xboole_0)),sK2,k1_xboole_0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f439,f96])).

fof(f96,plain,(
    ! [X0,X1] : ~ sP0(k1_xboole_0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ( r2_hidden(sK4(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(X2,sK4(X0,X1,X2)),X1)
          & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X2,X4),X1)
          & r2_hidden(X4,k2_relat_1(X1)) )
     => ( r2_hidden(sK4(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X2,X4),X1)
            & r2_hidden(X4,k2_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f33,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f439,plain,
    ( sP0(k1_xboole_0,sK2,sK3(k10_relat_1(sK2,k1_xboole_0)))
    | ~ sP1(sK3(k10_relat_1(sK2,k1_xboole_0)),sK2,k1_xboole_0)
    | ~ spl5_5 ),
    inference(resolution,[],[f37,f82])).

fof(f82,plain,
    ( r2_hidden(sK3(k10_relat_1(sK2,k1_xboole_0)),k10_relat_1(sK2,k1_xboole_0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k10_relat_1(sK2,k1_xboole_0)),k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X1,X2))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,k10_relat_1(X1,X2)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f83,plain,
    ( spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f70,f60,f80])).

fof(f60,plain,
    ( spl5_3
  <=> v1_xboole_0(k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f70,plain,
    ( r2_hidden(sK3(k10_relat_1(sK2,k1_xboole_0)),k10_relat_1(sK2,k1_xboole_0))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f62,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f62,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK2,k1_xboole_0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f56,f47,f60])).

fof(f47,plain,
    ( spl5_1
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f56,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK2,k1_xboole_0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f49,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f49,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f55,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f50,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f47])).

fof(f29,plain,(
    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:57:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.46  % (32407)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.46  % (32412)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.47  % (32415)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.23/0.47  % (32400)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.48  % (32400)Refutation not found, incomplete strategy% (32400)------------------------------
% 0.23/0.48  % (32400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (32400)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.48  
% 0.23/0.48  % (32400)Memory used [KB]: 10490
% 0.23/0.48  % (32400)Time elapsed: 0.061 s
% 0.23/0.48  % (32400)------------------------------
% 0.23/0.48  % (32400)------------------------------
% 0.23/0.48  % (32418)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.23/0.49  % (32399)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.49  % (32403)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.49  % (32404)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.49  % (32415)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f454,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f50,f55,f63,f83,f451])).
% 0.23/0.49  fof(f451,plain,(
% 0.23/0.49    ~spl5_2 | ~spl5_5),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f450])).
% 0.23/0.49  fof(f450,plain,(
% 0.23/0.49    $false | (~spl5_2 | ~spl5_5)),
% 0.23/0.49    inference(subsumption_resolution,[],[f449,f95])).
% 0.23/0.49  fof(f95,plain,(
% 0.23/0.49    ( ! [X0,X1] : (sP1(X0,sK2,X1)) ) | ~spl5_2),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f54,f43])).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~v1_relat_1(X2))),
% 0.23/0.49    inference(definition_folding,[],[f10,f12,f11])).
% 0.23/0.49  fof(f11,plain,(
% 0.23/0.49    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))))),
% 0.23/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    ! [X0,X2,X1] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.23/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.23/0.49  fof(f10,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.23/0.49    inference(ennf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    v1_relat_1(sK2) | ~spl5_2),
% 0.23/0.49    inference(avatar_component_clause,[],[f52])).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    spl5_2 <=> v1_relat_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.23/0.49  fof(f449,plain,(
% 0.23/0.49    ~sP1(sK3(k10_relat_1(sK2,k1_xboole_0)),sK2,k1_xboole_0) | ~spl5_5),
% 0.23/0.49    inference(subsumption_resolution,[],[f439,f96])).
% 0.23/0.49  fof(f96,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~sP0(k1_xboole_0,X0,X1)) )),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f66,f41])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | ~sP0(X0,X1,X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f27])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) => (r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X1))))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.23/0.49    inference(rectify,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~sP0(X1,X2,X0)))),
% 0.23/0.49    inference(nnf_transformation,[],[f11])).
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.49    inference(superposition,[],[f33,f44])).
% 0.23/0.49  fof(f44,plain,(
% 0.23/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.49    inference(equality_resolution,[],[f36])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.49    inference(flattening,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.49    inference(nnf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.23/0.49  fof(f439,plain,(
% 0.23/0.49    sP0(k1_xboole_0,sK2,sK3(k10_relat_1(sK2,k1_xboole_0))) | ~sP1(sK3(k10_relat_1(sK2,k1_xboole_0)),sK2,k1_xboole_0) | ~spl5_5),
% 0.23/0.49    inference(resolution,[],[f37,f82])).
% 0.23/0.49  fof(f82,plain,(
% 0.23/0.49    r2_hidden(sK3(k10_relat_1(sK2,k1_xboole_0)),k10_relat_1(sK2,k1_xboole_0)) | ~spl5_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f80])).
% 0.23/0.49  fof(f80,plain,(
% 0.23/0.49    spl5_5 <=> r2_hidden(sK3(k10_relat_1(sK2,k1_xboole_0)),k10_relat_1(sK2,k1_xboole_0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X1,X2)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,k10_relat_1(X1,X2)))) | ~sP1(X0,X1,X2))),
% 0.23/0.49    inference(rectify,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0,X2,X1] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~sP1(X0,X2,X1))),
% 0.23/0.49    inference(nnf_transformation,[],[f12])).
% 0.23/0.49  fof(f83,plain,(
% 0.23/0.49    spl5_5 | spl5_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f70,f60,f80])).
% 0.23/0.49  fof(f60,plain,(
% 0.23/0.49    spl5_3 <=> v1_xboole_0(k10_relat_1(sK2,k1_xboole_0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.23/0.49  fof(f70,plain,(
% 0.23/0.49    r2_hidden(sK3(k10_relat_1(sK2,k1_xboole_0)),k10_relat_1(sK2,k1_xboole_0)) | spl5_3),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f62,f32])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.49    inference(rectify,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.49    inference(nnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.49  fof(f62,plain,(
% 0.23/0.49    ~v1_xboole_0(k10_relat_1(sK2,k1_xboole_0)) | spl5_3),
% 0.23/0.49    inference(avatar_component_clause,[],[f60])).
% 0.23/0.49  fof(f63,plain,(
% 0.23/0.49    ~spl5_3 | spl5_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f56,f47,f60])).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    spl5_1 <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.49  fof(f56,plain,(
% 0.23/0.49    ~v1_xboole_0(k10_relat_1(sK2,k1_xboole_0)) | spl5_1),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f49,f30])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,plain,(
% 0.23/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.23/0.49  fof(f49,plain,(
% 0.23/0.49    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) | spl5_1),
% 0.23/0.49    inference(avatar_component_clause,[],[f47])).
% 0.23/0.49  fof(f55,plain,(
% 0.23/0.49    spl5_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f28,f52])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    v1_relat_1(sK2)),
% 0.23/0.49    inference(cnf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) & v1_relat_1(sK2)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) & v1_relat_1(sK2))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f8,plain,(
% 0.23/0.49    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,negated_conjecture,(
% 0.23/0.49    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.23/0.49    inference(negated_conjecture,[],[f6])).
% 0.23/0.49  fof(f6,conjecture,(
% 0.23/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    ~spl5_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f29,f47])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)),
% 0.23/0.49    inference(cnf_transformation,[],[f15])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (32415)------------------------------
% 0.23/0.49  % (32415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (32415)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (32415)Memory used [KB]: 10874
% 0.23/0.49  % (32415)Time elapsed: 0.082 s
% 0.23/0.49  % (32415)------------------------------
% 0.23/0.49  % (32415)------------------------------
% 0.23/0.49  % (32398)Success in time 0.125 s
%------------------------------------------------------------------------------
