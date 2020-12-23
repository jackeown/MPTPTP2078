%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:01 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 161 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  221 ( 418 expanded)
%              Number of equality atoms :   44 ( 112 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f84,f102,f127,f153,f156,f263,f373])).

fof(f373,plain,
    ( spl10_1
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f18,f49,f354])).

fof(f354,plain,
    ( ! [X0] :
        ( sK0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f353,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f353,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK5(sK0,X3,X4),X4)
        | sK0 = X4 )
    | ~ spl10_8 ),
    inference(forward_demodulation,[],[f271,f315])).

fof(f315,plain,
    ( ! [X0] : sK0 = k2_zfmisc_1(sK0,X0)
    | ~ spl10_8 ),
    inference(resolution,[],[f279,f287])).

fof(f287,plain,
    ( ! [X8,X7] : r1_tarski(k2_zfmisc_1(sK0,X7),X8)
    | ~ spl10_8 ),
    inference(resolution,[],[f270,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f270,plain,
    ( ! [X2,X1] : ~ r2_hidden(X1,k2_zfmisc_1(sK0,X2))
    | ~ spl10_8 ),
    inference(resolution,[],[f94,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f94,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl10_8
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | sK0 = X0 )
    | ~ spl10_8 ),
    inference(resolution,[],[f272,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f272,plain,
    ( ! [X5] : ~ r2_xboole_0(X5,sK0)
    | ~ spl10_8 ),
    inference(resolution,[],[f94,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

% (26233)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f271,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK5(sK0,X3,X4),X4)
        | k2_zfmisc_1(sK0,X3) = X4 )
    | ~ spl10_8 ),
    inference(resolution,[],[f94,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

% (26244)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f263,plain,
    ( spl10_2
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl10_2
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f18,f54,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f245,f20])).

fof(f245,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK5(sK1,X3,X4),X4)
        | sK1 = X4 )
    | ~ spl10_5 ),
    inference(forward_demodulation,[],[f162,f204])).

fof(f204,plain,
    ( ! [X0] : sK1 = k2_zfmisc_1(sK1,X0)
    | ~ spl10_5 ),
    inference(resolution,[],[f170,f175])).

fof(f175,plain,
    ( ! [X8,X7] : r1_tarski(k2_zfmisc_1(sK1,X7),X8)
    | ~ spl10_5 ),
    inference(resolution,[],[f161,f22])).

fof(f161,plain,
    ( ! [X2,X1] : ~ r2_hidden(X1,k2_zfmisc_1(sK1,X2))
    | ~ spl10_5 ),
    inference(resolution,[],[f80,f45])).

fof(f80,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl10_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0 )
    | ~ spl10_5 ),
    inference(resolution,[],[f163,f26])).

fof(f163,plain,
    ( ! [X5] : ~ r2_xboole_0(X5,sK1)
    | ~ spl10_5 ),
    inference(resolution,[],[f80,f27])).

fof(f162,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK5(sK1,X3,X4),X4)
        | k2_zfmisc_1(sK1,X3) = X4 )
    | ~ spl10_5 ),
    inference(resolution,[],[f80,f30])).

fof(f54,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f156,plain,
    ( spl10_3
    | ~ spl10_9
    | spl10_14 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl10_3
    | ~ spl10_9
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f101,f59,f152,f26])).

fof(f152,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl10_14
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f59,plain,
    ( sK0 != sK1
    | spl10_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl10_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f101,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl10_9
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f153,plain,
    ( ~ spl10_14
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f148,f125,f150])).

fof(f125,plain,
    ( spl10_12
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f148,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ spl10_12 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1)
    | ~ spl10_12 ),
    inference(resolution,[],[f142,f27])).

fof(f142,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(sK0,X2),sK1)
        | ~ r2_xboole_0(sK0,X2) )
    | ~ spl10_12 ),
    inference(resolution,[],[f126,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl10_8
    | spl10_12
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f74,f62,f125,f93])).

fof(f62,plain,
    ( spl10_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f67,f39])).

% (26233)Refutation not found, incomplete strategy% (26233)------------------------------
% (26233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26233)Termination reason: Refutation not found, incomplete strategy

% (26233)Memory used [KB]: 10618
% (26233)Time elapsed: 0.118 s
% (26233)------------------------------
% (26233)------------------------------
fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f67,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl10_4 ),
    inference(superposition,[],[f38,f64])).

fof(f64,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f62])).

% (26234)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f102,plain,
    ( spl10_9
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f97,f82,f99])).

fof(f82,plain,
    ( spl10_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f97,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f86,f22])).

fof(f86,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK1),sK0)
        | r1_tarski(X1,sK1) )
    | ~ spl10_6 ),
    inference(resolution,[],[f83,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl10_5
    | spl10_6
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f70,f62,f82,f79])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f66,f39])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl10_4 ),
    inference(superposition,[],[f37,f64])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f14,f62])).

fof(f14,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f60,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f17,f57])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f16,f52])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f15,f47])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:08:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.13/0.51  % (26238)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.13/0.51  % (26230)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.13/0.52  % (26222)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.13/0.52  % (26217)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.13/0.52  % (26216)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.13/0.52  % (26216)Refutation not found, incomplete strategy% (26216)------------------------------
% 1.13/0.52  % (26216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.52  % (26216)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.52  
% 1.13/0.52  % (26216)Memory used [KB]: 1663
% 1.13/0.52  % (26216)Time elapsed: 0.102 s
% 1.13/0.52  % (26216)------------------------------
% 1.13/0.52  % (26216)------------------------------
% 1.13/0.53  % (26219)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.13/0.53  % (26223)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.13/0.53  % (26218)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.13/0.53  % (26240)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.13/0.53  % (26224)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.13/0.53  % (26221)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.13/0.54  % (26220)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.13/0.54  % (26238)Refutation found. Thanks to Tanya!
% 1.13/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % (26232)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  % (26235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  fof(f374,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f84,f102,f127,f153,f156,f263,f373])).
% 1.34/0.54  fof(f373,plain,(
% 1.34/0.54    spl10_1 | ~spl10_8),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f357])).
% 1.34/0.54  fof(f357,plain,(
% 1.34/0.54    $false | (spl10_1 | ~spl10_8)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f18,f49,f354])).
% 1.34/0.54  fof(f354,plain,(
% 1.34/0.54    ( ! [X0] : (sK0 = X0 | ~v1_xboole_0(X0)) ) | ~spl10_8),
% 1.34/0.54    inference(resolution,[],[f353,f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.54  fof(f353,plain,(
% 1.34/0.54    ( ! [X4,X3] : (r2_hidden(sK5(sK0,X3,X4),X4) | sK0 = X4) ) | ~spl10_8),
% 1.34/0.54    inference(forward_demodulation,[],[f271,f315])).
% 1.34/0.54  fof(f315,plain,(
% 1.34/0.54    ( ! [X0] : (sK0 = k2_zfmisc_1(sK0,X0)) ) | ~spl10_8),
% 1.34/0.54    inference(resolution,[],[f279,f287])).
% 1.34/0.54  fof(f287,plain,(
% 1.34/0.54    ( ! [X8,X7] : (r1_tarski(k2_zfmisc_1(sK0,X7),X8)) ) | ~spl10_8),
% 1.34/0.54    inference(resolution,[],[f270,f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,plain,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.54  fof(f270,plain,(
% 1.34/0.54    ( ! [X2,X1] : (~r2_hidden(X1,k2_zfmisc_1(sK0,X2))) ) | ~spl10_8),
% 1.34/0.54    inference(resolution,[],[f94,f45])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(equality_resolution,[],[f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.34/0.54  fof(f94,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl10_8),
% 1.34/0.54    inference(avatar_component_clause,[],[f93])).
% 1.34/0.54  fof(f93,plain,(
% 1.34/0.54    spl10_8 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.34/0.54  fof(f279,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0) ) | ~spl10_8),
% 1.34/0.54    inference(resolution,[],[f272,f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.34/0.54  fof(f272,plain,(
% 1.34/0.54    ( ! [X5] : (~r2_xboole_0(X5,sK0)) ) | ~spl10_8),
% 1.34/0.54    inference(resolution,[],[f94,f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,plain,(
% 1.34/0.54    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.34/0.54  % (26233)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  fof(f271,plain,(
% 1.34/0.54    ( ! [X4,X3] : (r2_hidden(sK5(sK0,X3,X4),X4) | k2_zfmisc_1(sK0,X3) = X4) ) | ~spl10_8),
% 1.34/0.54    inference(resolution,[],[f94,f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    k1_xboole_0 != sK0 | spl10_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f47])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    spl10_1 <=> k1_xboole_0 = sK0),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    v1_xboole_0(k1_xboole_0)),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  % (26244)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    v1_xboole_0(k1_xboole_0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.34/0.54  fof(f263,plain,(
% 1.34/0.54    spl10_2 | ~spl10_5),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f248])).
% 1.34/0.54  fof(f248,plain,(
% 1.34/0.54    $false | (spl10_2 | ~spl10_5)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f18,f54,f246])).
% 1.34/0.54  fof(f246,plain,(
% 1.34/0.54    ( ! [X0] : (sK1 = X0 | ~v1_xboole_0(X0)) ) | ~spl10_5),
% 1.34/0.54    inference(resolution,[],[f245,f20])).
% 1.34/0.54  fof(f245,plain,(
% 1.34/0.54    ( ! [X4,X3] : (r2_hidden(sK5(sK1,X3,X4),X4) | sK1 = X4) ) | ~spl10_5),
% 1.34/0.54    inference(forward_demodulation,[],[f162,f204])).
% 1.34/0.54  fof(f204,plain,(
% 1.34/0.54    ( ! [X0] : (sK1 = k2_zfmisc_1(sK1,X0)) ) | ~spl10_5),
% 1.34/0.54    inference(resolution,[],[f170,f175])).
% 1.34/0.54  fof(f175,plain,(
% 1.34/0.54    ( ! [X8,X7] : (r1_tarski(k2_zfmisc_1(sK1,X7),X8)) ) | ~spl10_5),
% 1.34/0.54    inference(resolution,[],[f161,f22])).
% 1.34/0.54  fof(f161,plain,(
% 1.34/0.54    ( ! [X2,X1] : (~r2_hidden(X1,k2_zfmisc_1(sK1,X2))) ) | ~spl10_5),
% 1.34/0.54    inference(resolution,[],[f80,f45])).
% 1.34/0.54  fof(f80,plain,(
% 1.34/0.54    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl10_5),
% 1.34/0.54    inference(avatar_component_clause,[],[f79])).
% 1.34/0.54  fof(f79,plain,(
% 1.34/0.54    spl10_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.34/0.54  fof(f170,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0) ) | ~spl10_5),
% 1.34/0.54    inference(resolution,[],[f163,f26])).
% 1.34/0.54  fof(f163,plain,(
% 1.34/0.54    ( ! [X5] : (~r2_xboole_0(X5,sK1)) ) | ~spl10_5),
% 1.34/0.54    inference(resolution,[],[f80,f27])).
% 1.34/0.54  fof(f162,plain,(
% 1.34/0.54    ( ! [X4,X3] : (r2_hidden(sK5(sK1,X3,X4),X4) | k2_zfmisc_1(sK1,X3) = X4) ) | ~spl10_5),
% 1.34/0.54    inference(resolution,[],[f80,f30])).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    k1_xboole_0 != sK1 | spl10_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    spl10_2 <=> k1_xboole_0 = sK1),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.34/0.54  fof(f156,plain,(
% 1.34/0.54    spl10_3 | ~spl10_9 | spl10_14),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f154])).
% 1.34/0.54  fof(f154,plain,(
% 1.34/0.54    $false | (spl10_3 | ~spl10_9 | spl10_14)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f101,f59,f152,f26])).
% 1.34/0.54  fof(f152,plain,(
% 1.34/0.54    ~r2_xboole_0(sK0,sK1) | spl10_14),
% 1.34/0.54    inference(avatar_component_clause,[],[f150])).
% 1.34/0.54  fof(f150,plain,(
% 1.34/0.54    spl10_14 <=> r2_xboole_0(sK0,sK1)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    sK0 != sK1 | spl10_3),
% 1.34/0.54    inference(avatar_component_clause,[],[f57])).
% 1.34/0.54  fof(f57,plain,(
% 1.34/0.54    spl10_3 <=> sK0 = sK1),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.34/0.54  fof(f101,plain,(
% 1.34/0.54    r1_tarski(sK0,sK1) | ~spl10_9),
% 1.34/0.54    inference(avatar_component_clause,[],[f99])).
% 1.34/0.54  fof(f99,plain,(
% 1.34/0.54    spl10_9 <=> r1_tarski(sK0,sK1)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.34/0.54  fof(f153,plain,(
% 1.34/0.54    ~spl10_14 | ~spl10_12),
% 1.34/0.54    inference(avatar_split_clause,[],[f148,f125,f150])).
% 1.34/0.54  fof(f125,plain,(
% 1.34/0.54    spl10_12 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.34/0.54  fof(f148,plain,(
% 1.34/0.54    ~r2_xboole_0(sK0,sK1) | ~spl10_12),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f147])).
% 1.34/0.54  fof(f147,plain,(
% 1.34/0.54    ~r2_xboole_0(sK0,sK1) | ~r2_xboole_0(sK0,sK1) | ~spl10_12),
% 1.34/0.54    inference(resolution,[],[f142,f27])).
% 1.34/0.54  fof(f142,plain,(
% 1.34/0.54    ( ! [X2] : (~r2_hidden(sK4(sK0,X2),sK1) | ~r2_xboole_0(sK0,X2)) ) | ~spl10_12),
% 1.34/0.54    inference(resolution,[],[f126,f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f126,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl10_12),
% 1.34/0.54    inference(avatar_component_clause,[],[f125])).
% 1.34/0.54  fof(f127,plain,(
% 1.34/0.54    spl10_8 | spl10_12 | ~spl10_4),
% 1.34/0.54    inference(avatar_split_clause,[],[f74,f62,f125,f93])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    spl10_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.34/0.54  fof(f74,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl10_4),
% 1.34/0.54    inference(resolution,[],[f67,f39])).
% 1.34/0.54  % (26233)Refutation not found, incomplete strategy% (26233)------------------------------
% 1.34/0.54  % (26233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (26233)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (26233)Memory used [KB]: 10618
% 1.34/0.54  % (26233)Time elapsed: 0.118 s
% 1.34/0.54  % (26233)------------------------------
% 1.34/0.54  % (26233)------------------------------
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl10_4),
% 1.34/0.54    inference(superposition,[],[f38,f64])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl10_4),
% 1.34/0.54    inference(avatar_component_clause,[],[f62])).
% 1.34/0.54  % (26234)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    spl10_9 | ~spl10_6),
% 1.34/0.54    inference(avatar_split_clause,[],[f97,f82,f99])).
% 1.34/0.54  fof(f82,plain,(
% 1.34/0.54    spl10_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.34/0.54  fof(f97,plain,(
% 1.34/0.54    r1_tarski(sK0,sK1) | ~spl10_6),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f96])).
% 1.34/0.54  fof(f96,plain,(
% 1.34/0.54    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl10_6),
% 1.34/0.54    inference(resolution,[],[f86,f22])).
% 1.34/0.54  fof(f86,plain,(
% 1.34/0.54    ( ! [X1] : (~r2_hidden(sK3(X1,sK1),sK0) | r1_tarski(X1,sK1)) ) | ~spl10_6),
% 1.34/0.54    inference(resolution,[],[f83,f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f12])).
% 1.34/0.54  fof(f83,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl10_6),
% 1.34/0.54    inference(avatar_component_clause,[],[f82])).
% 1.34/0.54  fof(f84,plain,(
% 1.34/0.54    spl10_5 | spl10_6 | ~spl10_4),
% 1.34/0.54    inference(avatar_split_clause,[],[f70,f62,f82,f79])).
% 1.34/0.54  fof(f70,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl10_4),
% 1.34/0.54    inference(resolution,[],[f66,f39])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl10_4),
% 1.34/0.54    inference(superposition,[],[f37,f64])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    spl10_4),
% 1.34/0.54    inference(avatar_split_clause,[],[f14,f62])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,plain,(
% 1.34/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.34/0.54    inference(flattening,[],[f10])).
% 1.34/0.54  fof(f10,plain,(
% 1.34/0.54    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.54    inference(negated_conjecture,[],[f8])).
% 1.34/0.54  fof(f8,conjecture,(
% 1.34/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ~spl10_3),
% 1.34/0.54    inference(avatar_split_clause,[],[f17,f57])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    sK0 != sK1),
% 1.34/0.54    inference(cnf_transformation,[],[f11])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    ~spl10_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f16,f52])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    k1_xboole_0 != sK1),
% 1.34/0.54    inference(cnf_transformation,[],[f11])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ~spl10_1),
% 1.34/0.54    inference(avatar_split_clause,[],[f15,f47])).
% 1.34/0.54  fof(f15,plain,(
% 1.34/0.54    k1_xboole_0 != sK0),
% 1.34/0.54    inference(cnf_transformation,[],[f11])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (26238)------------------------------
% 1.34/0.54  % (26238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (26238)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (26238)Memory used [KB]: 10874
% 1.34/0.54  % (26238)Time elapsed: 0.064 s
% 1.34/0.54  % (26238)------------------------------
% 1.34/0.54  % (26238)------------------------------
% 1.34/0.54  % (26215)Success in time 0.175 s
%------------------------------------------------------------------------------
