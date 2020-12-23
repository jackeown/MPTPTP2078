%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:15 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 102 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  153 ( 229 expanded)
%              Number of equality atoms :   98 ( 150 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f69,f86,f102,f127,f135,f170,f198])).

fof(f198,plain,
    ( spl2_5
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl2_5
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f80,f80,f169,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f169,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_10
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f80,plain,
    ( k1_xboole_0 != sK0
    | spl2_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f170,plain,
    ( spl2_10
    | spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f160,f83,f79,f167])).

fof(f83,plain,
    ( spl2_6
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f160,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_6 ),
    inference(superposition,[],[f13,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f135,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl2_9 ),
    inference(unit_resulting_resolution,[],[f33,f126])).

fof(f126,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl2_9
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f33,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f127,plain,
    ( ~ spl2_9
    | spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f100,f79,f66,f124])).

fof(f66,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f100,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | spl2_4
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f96,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f96,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | spl2_4
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f68,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f68,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f102,plain,
    ( ~ spl2_3
    | spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f98,f79,f39,f62])).

fof(f62,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f39,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl2_1
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f41,f81])).

fof(f41,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f86,plain,
    ( spl2_1
    | spl2_5
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f77,f44,f83,f79,f39])).

fof(f44,plain,
    ( spl2_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f77,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK0
    | sK0 = sK1
    | ~ spl2_2 ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,
    ( ! [X8,X7] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) != k2_zfmisc_1(X7,X8)
        | k1_xboole_0 = X7
        | k1_xboole_0 = X8
        | sK1 = X8 )
    | ~ spl2_2 ),
    inference(superposition,[],[f19,f46])).

fof(f46,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f69,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f44,f66,f62])).

fof(f59,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(superposition,[],[f31,f46])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f11,f25,f25])).

fof(f11,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f42,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f12,f39])).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (27640)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.43/0.58  % (27649)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.77/0.59  % (27665)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.77/0.59  % (27649)Refutation not found, incomplete strategy% (27649)------------------------------
% 1.77/0.59  % (27649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (27639)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.77/0.59  % (27638)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.77/0.59  % (27638)Refutation not found, incomplete strategy% (27638)------------------------------
% 1.77/0.59  % (27638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (27638)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (27638)Memory used [KB]: 1663
% 1.77/0.59  % (27638)Time elapsed: 0.155 s
% 1.77/0.59  % (27638)------------------------------
% 1.77/0.59  % (27638)------------------------------
% 1.77/0.59  % (27649)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (27649)Memory used [KB]: 10618
% 1.77/0.59  % (27649)Time elapsed: 0.154 s
% 1.77/0.59  % (27649)------------------------------
% 1.77/0.59  % (27649)------------------------------
% 1.77/0.59  % (27663)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.77/0.59  % (27655)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.77/0.59  % (27655)Refutation not found, incomplete strategy% (27655)------------------------------
% 1.77/0.59  % (27655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.60  % (27643)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.77/0.60  % (27650)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.77/0.60  % (27652)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.77/0.60  % (27647)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.77/0.60  % (27655)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.60  
% 1.77/0.60  % (27655)Memory used [KB]: 1663
% 1.77/0.60  % (27655)Time elapsed: 0.158 s
% 1.77/0.60  % (27655)------------------------------
% 1.77/0.60  % (27655)------------------------------
% 1.77/0.60  % (27637)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.77/0.60  % (27663)Refutation not found, incomplete strategy% (27663)------------------------------
% 1.77/0.60  % (27663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.60  % (27663)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.60  
% 1.77/0.60  % (27663)Memory used [KB]: 6268
% 1.77/0.60  % (27663)Time elapsed: 0.164 s
% 1.77/0.60  % (27663)------------------------------
% 1.77/0.60  % (27663)------------------------------
% 1.77/0.60  % (27642)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.77/0.60  % (27665)Refutation found. Thanks to Tanya!
% 1.77/0.60  % SZS status Theorem for theBenchmark
% 1.77/0.60  % SZS output start Proof for theBenchmark
% 1.77/0.60  fof(f202,plain,(
% 1.77/0.60    $false),
% 1.77/0.60    inference(avatar_sat_refutation,[],[f42,f47,f69,f86,f102,f127,f135,f170,f198])).
% 1.77/0.60  fof(f198,plain,(
% 1.77/0.60    spl2_5 | ~spl2_10),
% 1.77/0.60    inference(avatar_contradiction_clause,[],[f184])).
% 1.77/0.60  fof(f184,plain,(
% 1.77/0.60    $false | (spl2_5 | ~spl2_10)),
% 1.77/0.60    inference(unit_resulting_resolution,[],[f80,f80,f169,f13])).
% 1.77/0.60  fof(f13,plain,(
% 1.77/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.77/0.60    inference(cnf_transformation,[],[f1])).
% 1.77/0.60  fof(f1,axiom,(
% 1.77/0.60    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.77/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.77/0.60  fof(f169,plain,(
% 1.77/0.60    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_10),
% 1.77/0.60    inference(avatar_component_clause,[],[f167])).
% 1.77/0.60  fof(f167,plain,(
% 1.77/0.60    spl2_10 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0)),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.77/0.60  fof(f80,plain,(
% 1.77/0.60    k1_xboole_0 != sK0 | spl2_5),
% 1.77/0.60    inference(avatar_component_clause,[],[f79])).
% 1.77/0.60  fof(f79,plain,(
% 1.77/0.60    spl2_5 <=> k1_xboole_0 = sK0),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.77/0.60  fof(f170,plain,(
% 1.77/0.60    spl2_10 | spl2_5 | ~spl2_6),
% 1.77/0.60    inference(avatar_split_clause,[],[f160,f83,f79,f167])).
% 1.77/0.60  fof(f83,plain,(
% 1.77/0.60    spl2_6 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.77/0.60  fof(f160,plain,(
% 1.77/0.60    k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_6),
% 1.77/0.60    inference(trivial_inequality_removal,[],[f152])).
% 1.77/0.60  fof(f152,plain,(
% 1.77/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_6),
% 1.77/0.60    inference(superposition,[],[f13,f85])).
% 1.77/0.60  fof(f85,plain,(
% 1.77/0.60    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | ~spl2_6),
% 1.77/0.60    inference(avatar_component_clause,[],[f83])).
% 1.77/0.60  fof(f135,plain,(
% 1.77/0.60    spl2_9),
% 1.77/0.60    inference(avatar_contradiction_clause,[],[f128])).
% 1.77/0.60  fof(f128,plain,(
% 1.77/0.60    $false | spl2_9),
% 1.77/0.60    inference(unit_resulting_resolution,[],[f33,f126])).
% 1.77/0.60  fof(f126,plain,(
% 1.77/0.60    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | spl2_9),
% 1.77/0.60    inference(avatar_component_clause,[],[f124])).
% 1.77/0.60  fof(f124,plain,(
% 1.77/0.60    spl2_9 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.77/0.60  fof(f33,plain,(
% 1.77/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.77/0.60    inference(equality_resolution,[],[f14])).
% 1.77/0.60  fof(f14,plain,(
% 1.77/0.60    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.77/0.60    inference(cnf_transformation,[],[f1])).
% 1.77/0.60  fof(f127,plain,(
% 1.77/0.60    ~spl2_9 | spl2_4 | ~spl2_5),
% 1.77/0.60    inference(avatar_split_clause,[],[f100,f79,f66,f124])).
% 1.77/0.60  fof(f66,plain,(
% 1.77/0.60    spl2_4 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.77/0.60  fof(f100,plain,(
% 1.77/0.60    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (spl2_4 | ~spl2_5)),
% 1.77/0.60    inference(forward_demodulation,[],[f96,f32])).
% 1.77/0.60  fof(f32,plain,(
% 1.77/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.77/0.60    inference(equality_resolution,[],[f15])).
% 1.77/0.60  fof(f15,plain,(
% 1.77/0.60    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.77/0.60    inference(cnf_transformation,[],[f1])).
% 1.77/0.60  fof(f96,plain,(
% 1.77/0.60    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | (spl2_4 | ~spl2_5)),
% 1.77/0.60    inference(backward_demodulation,[],[f68,f81])).
% 1.77/0.60  fof(f81,plain,(
% 1.77/0.60    k1_xboole_0 = sK0 | ~spl2_5),
% 1.77/0.60    inference(avatar_component_clause,[],[f79])).
% 1.77/0.60  fof(f68,plain,(
% 1.77/0.60    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | spl2_4),
% 1.77/0.60    inference(avatar_component_clause,[],[f66])).
% 1.77/0.60  fof(f102,plain,(
% 1.77/0.60    ~spl2_3 | spl2_1 | ~spl2_5),
% 1.77/0.60    inference(avatar_split_clause,[],[f98,f79,f39,f62])).
% 1.77/0.60  fof(f62,plain,(
% 1.77/0.60    spl2_3 <=> k1_xboole_0 = sK1),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.77/0.60  fof(f39,plain,(
% 1.77/0.60    spl2_1 <=> sK0 = sK1),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.77/0.60  fof(f98,plain,(
% 1.77/0.60    k1_xboole_0 != sK1 | (spl2_1 | ~spl2_5)),
% 1.77/0.60    inference(backward_demodulation,[],[f41,f81])).
% 1.77/0.60  fof(f41,plain,(
% 1.77/0.60    sK0 != sK1 | spl2_1),
% 1.77/0.60    inference(avatar_component_clause,[],[f39])).
% 1.77/0.60  fof(f86,plain,(
% 1.77/0.60    spl2_1 | spl2_5 | spl2_6 | ~spl2_2),
% 1.77/0.60    inference(avatar_split_clause,[],[f77,f44,f83,f79,f39])).
% 1.77/0.60  fof(f44,plain,(
% 1.77/0.60    spl2_2 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.77/0.60  fof(f77,plain,(
% 1.77/0.60    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0 | sK0 = sK1 | ~spl2_2),
% 1.77/0.60    inference(equality_resolution,[],[f55])).
% 1.77/0.60  fof(f55,plain,(
% 1.77/0.60    ( ! [X8,X7] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) != k2_zfmisc_1(X7,X8) | k1_xboole_0 = X7 | k1_xboole_0 = X8 | sK1 = X8) ) | ~spl2_2),
% 1.77/0.60    inference(superposition,[],[f19,f46])).
% 1.77/0.60  fof(f46,plain,(
% 1.77/0.60    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) | ~spl2_2),
% 1.77/0.60    inference(avatar_component_clause,[],[f44])).
% 1.77/0.60  fof(f19,plain,(
% 1.77/0.60    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X1 = X3) )),
% 1.77/0.60    inference(cnf_transformation,[],[f10])).
% 1.77/0.60  fof(f10,plain,(
% 1.77/0.60    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.77/0.60    inference(flattening,[],[f9])).
% 1.77/0.60  fof(f9,plain,(
% 1.77/0.60    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.77/0.60    inference(ennf_transformation,[],[f2])).
% 1.77/0.60  fof(f2,axiom,(
% 1.77/0.60    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.77/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.77/0.60  fof(f69,plain,(
% 1.77/0.60    spl2_3 | ~spl2_4 | ~spl2_2),
% 1.77/0.60    inference(avatar_split_clause,[],[f59,f44,f66,f62])).
% 1.77/0.60  fof(f59,plain,(
% 1.77/0.60    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | ~spl2_2),
% 1.77/0.60    inference(duplicate_literal_removal,[],[f50])).
% 1.77/0.60  fof(f50,plain,(
% 1.77/0.60    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~spl2_2),
% 1.77/0.60    inference(superposition,[],[f31,f46])).
% 1.77/0.60  fof(f31,plain,(
% 1.77/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.77/0.60    inference(definition_unfolding,[],[f20,f25])).
% 1.77/0.60  fof(f25,plain,(
% 1.77/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.77/0.60    inference(definition_unfolding,[],[f17,f16])).
% 1.77/0.60  fof(f16,plain,(
% 1.77/0.60    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.77/0.60    inference(cnf_transformation,[],[f3])).
% 1.77/0.60  fof(f3,axiom,(
% 1.77/0.60    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.77/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.77/0.60  fof(f17,plain,(
% 1.77/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.77/0.60    inference(cnf_transformation,[],[f4])).
% 1.77/0.60  fof(f4,axiom,(
% 1.77/0.60    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.77/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.77/0.60  fof(f20,plain,(
% 1.77/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.77/0.60    inference(cnf_transformation,[],[f5])).
% 1.77/0.60  fof(f5,axiom,(
% 1.77/0.60    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.77/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.77/0.60  fof(f47,plain,(
% 1.77/0.60    spl2_2),
% 1.77/0.60    inference(avatar_split_clause,[],[f26,f44])).
% 1.77/0.60  fof(f26,plain,(
% 1.77/0.60    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 1.77/0.60    inference(definition_unfolding,[],[f11,f25,f25])).
% 1.77/0.60  fof(f11,plain,(
% 1.77/0.60    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 1.77/0.60    inference(cnf_transformation,[],[f8])).
% 1.77/0.60  fof(f8,plain,(
% 1.77/0.60    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 1.77/0.60    inference(ennf_transformation,[],[f7])).
% 1.77/0.60  fof(f7,negated_conjecture,(
% 1.77/0.60    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 1.77/0.60    inference(negated_conjecture,[],[f6])).
% 1.77/0.60  fof(f6,conjecture,(
% 1.77/0.60    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 1.77/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 1.77/0.60  fof(f42,plain,(
% 1.77/0.60    ~spl2_1),
% 1.77/0.60    inference(avatar_split_clause,[],[f12,f39])).
% 1.77/0.60  fof(f12,plain,(
% 1.77/0.60    sK0 != sK1),
% 1.77/0.60    inference(cnf_transformation,[],[f8])).
% 1.77/0.60  % SZS output end Proof for theBenchmark
% 1.77/0.60  % (27665)------------------------------
% 1.77/0.60  % (27665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.60  % (27665)Termination reason: Refutation
% 1.77/0.60  
% 1.77/0.60  % (27665)Memory used [KB]: 10746
% 1.77/0.60  % (27665)Time elapsed: 0.154 s
% 1.77/0.60  % (27665)------------------------------
% 1.77/0.60  % (27665)------------------------------
% 1.77/0.60  % (27666)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.77/0.60  % (27648)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.77/0.60  % (27645)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.77/0.60  % (27636)Success in time 0.237 s
%------------------------------------------------------------------------------
