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
% DateTime   : Thu Dec  3 12:50:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  81 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 223 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f63,f69,f87,f1200])).

fof(f1200,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f1199])).

fof(f1199,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f1177,f370])).

fof(f370,plain,(
    ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
      & ( ( r2_hidden(sK5(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X2,X4),X1) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X2,X4),X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X0,X3] :
      ( ( sP0(X1,X0,X3)
        | ! [X4] :
            ( ~ r2_hidden(X4,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X3,X4),X0) )
        | ~ sP0(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f11])).

% (26092)Refutation not found, incomplete strategy% (26092)------------------------------
% (26092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26092)Termination reason: Refutation not found, incomplete strategy

% (26092)Memory used [KB]: 1535
% (26092)Time elapsed: 0.077 s
% (26092)------------------------------
% (26092)------------------------------
fof(f11,plain,(
    ! [X1,X0,X3] :
      ( sP0(X1,X0,X3)
    <=> ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X3,X4),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f70,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f41,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f1177,plain,
    ( sP0(sK3,k1_xboole_0,sK4(k1_xboole_0,sK3,k1_xboole_0))
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f86,f70,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,sK4(X0,X1,X2))
      | sP1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,X0,sK4(X0,X1,X2))
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sP0(X1,X0,sK4(X0,X1,X2))
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,X0,sK4(X0,X1,X2))
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sP0(X1,X0,sK4(X0,X1,X2))
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X0,X3) )
            & ( sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f86,plain,
    ( ~ sP1(k1_xboole_0,sK3,k1_xboole_0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_5
  <=> sP1(k1_xboole_0,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f87,plain,
    ( ~ spl6_5
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f76,f66,f49,f84])).

fof(f49,plain,
    ( spl6_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f66,plain,
    ( spl6_4
  <=> sP2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f76,plain,
    ( ~ sP1(k1_xboole_0,sK3,k1_xboole_0)
    | spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f68,f51,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ sP1(X0,X1,X2)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ~ sP1(X0,X1,X2) )
          & ( sP1(X0,X1,X2)
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> sP1(X0,X1,X2) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f51,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f68,plain,
    ( sP2(k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f64,f60,f66])).

% (26098)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f60,plain,
    ( spl6_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f64,plain,
    ( sP2(k1_xboole_0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f62,f40])).

fof(f40,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f13,f12,f11])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f62,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f58,f54,f60])).

fof(f54,plain,
    ( spl6_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f58,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f56,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f57,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f52,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f15])).

fof(f15,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (26087)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (26095)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (26079)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (26081)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (26093)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (26082)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (26082)Refutation not found, incomplete strategy% (26082)------------------------------
% 0.20/0.52  % (26082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26082)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26082)Memory used [KB]: 10490
% 0.20/0.52  % (26082)Time elapsed: 0.108 s
% 0.20/0.52  % (26082)------------------------------
% 0.20/0.52  % (26082)------------------------------
% 0.20/0.52  % (26092)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (26085)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (26095)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f1201,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f52,f57,f63,f69,f87,f1200])).
% 0.20/0.52  fof(f1200,plain,(
% 0.20/0.52    spl6_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f1199])).
% 0.20/0.52  fof(f1199,plain,(
% 0.20/0.52    $false | spl6_5),
% 0.20/0.52    inference(subsumption_resolution,[],[f1177,f370])).
% 0.20/0.52  fof(f370,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f70,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1)) => (r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1)) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X1,X0,X3] : ((sP0(X1,X0,X3) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~sP0(X1,X0,X3)))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  % (26092)Refutation not found, incomplete strategy% (26092)------------------------------
% 0.20/0.52  % (26092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26092)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26092)Memory used [KB]: 1535
% 0.20/0.52  % (26092)Time elapsed: 0.077 s
% 0.20/0.52  % (26092)------------------------------
% 0.20/0.52  % (26092)------------------------------
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X1,X0,X3] : (sP0(X1,X0,X3) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f41,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.52  fof(f1177,plain,(
% 0.20/0.52    sP0(sK3,k1_xboole_0,sK4(k1_xboole_0,sK3,k1_xboole_0)) | spl6_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f86,f70,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,sK4(X0,X1,X2)) | sP1(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,X0,sK4(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,X0,sK4(X0,X1,X2)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2))) => ((~sP0(X1,X0,sK4(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,X0,sK4(X0,X1,X2)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP0(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X0,X3)) & (sP0(X1,X0,X3) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.52    inference(nnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X0,X3)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ~sP1(k1_xboole_0,sK3,k1_xboole_0) | spl6_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl6_5 <=> sP1(k1_xboole_0,sK3,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ~spl6_5 | spl6_1 | ~spl6_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f76,f66,f49,f84])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl6_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl6_4 <=> sP2(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ~sP1(k1_xboole_0,sK3,k1_xboole_0) | (spl6_1 | ~spl6_4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f68,f51,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | ~sP1(X0,X1,X2) | ~sP2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k10_relat_1(X0,X1) != X2)) | ~sP2(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> sP1(X0,X1,X2)) | ~sP2(X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) | spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f49])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    sP2(k1_xboole_0) | ~spl6_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f66])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl6_4 | ~spl6_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f64,f60,f66])).
% 0.20/0.52  % (26098)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl6_3 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    sP2(k1_xboole_0) | ~spl6_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f62,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (sP2(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(definition_folding,[],[f10,f13,f12,f11])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    v1_relat_1(k1_xboole_0) | ~spl6_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f60])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl6_3 | ~spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f58,f54,f60])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl6_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    v1_relat_1(k1_xboole_0) | ~spl6_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f56,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0) | ~spl6_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f54])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f54])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ~spl6_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f49])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (26095)------------------------------
% 0.20/0.52  % (26095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26095)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (26095)Memory used [KB]: 11385
% 0.20/0.52  % (26095)Time elapsed: 0.089 s
% 0.20/0.52  % (26095)------------------------------
% 0.20/0.52  % (26095)------------------------------
% 0.20/0.52  % (26084)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (26078)Success in time 0.162 s
%------------------------------------------------------------------------------
