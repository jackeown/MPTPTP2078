%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:51 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 111 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  192 ( 299 expanded)
%              Number of equality atoms :   56 ( 105 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1818,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f172,f201,f290,f846,f1002,f1245,f1580,f1721,f1771,f1817])).

fof(f1817,plain,
    ( ~ spl12_9
    | ~ spl12_10
    | spl12_14 ),
    inference(avatar_contradiction_clause,[],[f1815])).

fof(f1815,plain,
    ( $false
    | ~ spl12_9
    | ~ spl12_10
    | spl12_14 ),
    inference(subsumption_resolution,[],[f1243,f1814])).

fof(f1814,plain,
    ( ~ r2_hidden(sK5(k1_tarski(sK0),sK0),sK0)
    | ~ spl12_9
    | spl12_14 ),
    inference(forward_demodulation,[],[f1770,f1749])).

fof(f1749,plain,
    ( sK0 = sK7(k1_tarski(sK0),sK0)
    | ~ spl12_9 ),
    inference(resolution,[],[f1240,f126])).

fof(f126,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1240,plain,
    ( r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f1238])).

fof(f1238,plain,
    ( spl12_9
  <=> r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f1770,plain,
    ( ~ r2_hidden(sK5(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0))
    | spl12_14 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f1768,plain,
    ( spl12_14
  <=> r2_hidden(sK5(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f1243,plain,
    ( r2_hidden(sK5(k1_tarski(sK0),sK0),sK0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f1242])).

fof(f1242,plain,
    ( spl12_10
  <=> r2_hidden(sK5(k1_tarski(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f1771,plain,
    ( ~ spl12_14
    | ~ spl12_10
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f940,f844,f1242,f1768])).

fof(f844,plain,
    ( spl12_7
  <=> ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK5(k1_tarski(sK0),X1),X1)
        | ~ r2_hidden(sK5(k1_tarski(sK0),X1),sK7(k1_tarski(sK0),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f940,plain,
    ( ~ r2_hidden(sK5(k1_tarski(sK0),sK0),sK0)
    | ~ r2_hidden(sK5(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0))
    | ~ spl12_7 ),
    inference(equality_resolution,[],[f845])).

fof(f845,plain,
    ( ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK5(k1_tarski(sK0),X1),X1)
        | ~ r2_hidden(sK5(k1_tarski(sK0),X1),sK7(k1_tarski(sK0),X1)) )
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f844])).

fof(f1721,plain,
    ( spl12_10
    | ~ spl12_13 ),
    inference(avatar_contradiction_clause,[],[f1713])).

fof(f1713,plain,
    ( $false
    | spl12_10
    | ~ spl12_13 ),
    inference(resolution,[],[f1682,f128])).

fof(f128,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1682,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl12_10
    | ~ spl12_13 ),
    inference(resolution,[],[f1579,f1244])).

fof(f1244,plain,
    ( ~ r2_hidden(sK5(k1_tarski(sK0),sK0),sK0)
    | spl12_10 ),
    inference(avatar_component_clause,[],[f1242])).

fof(f1579,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_tarski(sK0),sK0),X0)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f1578])).

fof(f1578,plain,
    ( spl12_13
  <=> ! [X0] :
        ( r2_hidden(sK5(k1_tarski(sK0),sK0),X0)
        | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f1580,plain,
    ( spl12_13
    | spl12_10
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f1026,f1000,f1242,f1578])).

fof(f1000,plain,
    ( spl12_8
  <=> ! [X3,X2] :
        ( sK0 != X2
        | r2_hidden(sK5(k1_tarski(sK0),X2),X2)
        | r2_hidden(sK5(k1_tarski(sK0),X2),X3)
        | ~ r2_hidden(X3,k1_tarski(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f1026,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_tarski(sK0),sK0),sK0)
        | r2_hidden(sK5(k1_tarski(sK0),sK0),X0)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl12_8 ),
    inference(equality_resolution,[],[f1001])).

fof(f1001,plain,
    ( ! [X2,X3] :
        ( sK0 != X2
        | r2_hidden(sK5(k1_tarski(sK0),X2),X2)
        | r2_hidden(sK5(k1_tarski(sK0),X2),X3)
        | ~ r2_hidden(X3,k1_tarski(sK0)) )
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1245,plain,
    ( spl12_9
    | ~ spl12_10
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f716,f199,f1242,f1238])).

fof(f199,plain,
    ( spl12_4
  <=> ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK5(k1_tarski(sK0),X0),X0)
        | r2_hidden(sK7(k1_tarski(sK0),X0),k1_tarski(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f716,plain,
    ( ~ r2_hidden(sK5(k1_tarski(sK0),sK0),sK0)
    | r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl12_4 ),
    inference(equality_resolution,[],[f200])).

fof(f200,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK5(k1_tarski(sK0),X0),X0)
        | r2_hidden(sK7(k1_tarski(sK0),X0),k1_tarski(sK0)) )
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1002,plain,
    ( spl12_3
    | spl12_8 ),
    inference(avatar_split_clause,[],[f139,f1000,f195])).

fof(f195,plain,
    ( spl12_3
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f139,plain,(
    ! [X2,X3] :
      ( sK0 != X2
      | k1_xboole_0 = k1_tarski(sK0)
      | ~ r2_hidden(X3,k1_tarski(sK0))
      | r2_hidden(sK5(k1_tarski(sK0),X2),X3)
      | r2_hidden(sK5(k1_tarski(sK0),X2),X2) ) ),
    inference(superposition,[],[f52,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK5(X0,X1),X3)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_setfam_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f52,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f846,plain,
    ( spl12_3
    | spl12_7 ),
    inference(avatar_split_clause,[],[f138,f844,f195])).

fof(f138,plain,(
    ! [X1] :
      ( sK0 != X1
      | k1_xboole_0 = k1_tarski(sK0)
      | ~ r2_hidden(sK5(k1_tarski(sK0),X1),sK7(k1_tarski(sK0),X1))
      | ~ r2_hidden(sK5(k1_tarski(sK0),X1),X1) ) ),
    inference(superposition,[],[f52,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(sK5(X0,X1),sK7(X0,X1))
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_setfam_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f290,plain,
    ( spl12_2
    | ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f150,f253])).

fof(f253,plain,
    ( k1_xboole_0 = sK0
    | ~ spl12_3 ),
    inference(forward_demodulation,[],[f235,f54])).

fof(f54,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f235,plain,
    ( k3_tarski(k1_xboole_0) = sK0
    | ~ spl12_3 ),
    inference(superposition,[],[f57,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f195])).

fof(f57,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f150,plain,
    ( k1_xboole_0 != sK0
    | spl12_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl12_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f201,plain,
    ( spl12_3
    | spl12_4 ),
    inference(avatar_split_clause,[],[f137,f199,f195])).

fof(f137,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = k1_tarski(sK0)
      | r2_hidden(sK7(k1_tarski(sK0),X0),k1_tarski(sK0))
      | ~ r2_hidden(sK5(k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK7(X0,X1),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_setfam_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f172,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl12_1 ),
    inference(resolution,[],[f146,f128])).

fof(f146,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl12_1
  <=> r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f151,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f142,f148,f144])).

fof(f142,plain,
    ( k1_xboole_0 != sK0
    | ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(inner_rewriting,[],[f140])).

fof(f140,plain,
    ( k1_xboole_0 != sK0
    | ~ r2_hidden(k1_xboole_0,k1_tarski(sK0)) ),
    inference(superposition,[],[f52,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (3802)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.46  % (3794)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (3790)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (3789)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (3785)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.22/0.51  % (3783)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.51  % (3783)Refutation not found, incomplete strategy% (3783)------------------------------
% 1.22/0.51  % (3783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (3783)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.51  
% 1.22/0.51  % (3783)Memory used [KB]: 10618
% 1.22/0.51  % (3783)Time elapsed: 0.099 s
% 1.22/0.51  % (3783)------------------------------
% 1.22/0.51  % (3783)------------------------------
% 1.22/0.51  % (3800)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.22/0.51  % (3782)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.22/0.52  % (3801)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.22/0.52  % (3788)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.22/0.52  % (3806)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.22/0.52  % (3786)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.22/0.52  % (3804)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.22/0.52  % (3805)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.22/0.52  % (3792)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.22/0.52  % (3793)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.38/0.53  % (3784)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.38/0.53  % (3797)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.38/0.53  % (3791)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.54  % (3799)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.38/0.54  % (3796)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.38/0.54  % (3787)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.38/0.54  % (3787)Refutation not found, incomplete strategy% (3787)------------------------------
% 1.38/0.54  % (3787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (3787)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (3787)Memory used [KB]: 6140
% 1.38/0.54  % (3787)Time elapsed: 0.130 s
% 1.38/0.54  % (3787)------------------------------
% 1.38/0.54  % (3787)------------------------------
% 1.38/0.54  % (3802)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.55  % (3807)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f1818,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(avatar_sat_refutation,[],[f151,f172,f201,f290,f846,f1002,f1245,f1580,f1721,f1771,f1817])).
% 1.38/0.55  fof(f1817,plain,(
% 1.38/0.55    ~spl12_9 | ~spl12_10 | spl12_14),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f1815])).
% 1.38/0.55  fof(f1815,plain,(
% 1.38/0.55    $false | (~spl12_9 | ~spl12_10 | spl12_14)),
% 1.38/0.55    inference(subsumption_resolution,[],[f1243,f1814])).
% 1.38/0.55  fof(f1814,plain,(
% 1.38/0.55    ~r2_hidden(sK5(k1_tarski(sK0),sK0),sK0) | (~spl12_9 | spl12_14)),
% 1.38/0.55    inference(forward_demodulation,[],[f1770,f1749])).
% 1.38/0.55  fof(f1749,plain,(
% 1.38/0.55    sK0 = sK7(k1_tarski(sK0),sK0) | ~spl12_9),
% 1.38/0.55    inference(resolution,[],[f1240,f126])).
% 1.38/0.55  fof(f126,plain,(
% 1.38/0.55    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k1_tarski(X0))) )),
% 1.38/0.55    inference(equality_resolution,[],[f96])).
% 1.38/0.55  fof(f96,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.38/0.55    inference(cnf_transformation,[],[f13])).
% 1.38/0.55  fof(f13,axiom,(
% 1.38/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.38/0.55  fof(f1240,plain,(
% 1.38/0.55    r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~spl12_9),
% 1.38/0.55    inference(avatar_component_clause,[],[f1238])).
% 1.38/0.55  fof(f1238,plain,(
% 1.38/0.55    spl12_9 <=> r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.38/0.55  fof(f1770,plain,(
% 1.38/0.55    ~r2_hidden(sK5(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0)) | spl12_14),
% 1.38/0.55    inference(avatar_component_clause,[],[f1768])).
% 1.38/0.55  fof(f1768,plain,(
% 1.38/0.55    spl12_14 <=> r2_hidden(sK5(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 1.38/0.55  fof(f1243,plain,(
% 1.38/0.55    r2_hidden(sK5(k1_tarski(sK0),sK0),sK0) | ~spl12_10),
% 1.38/0.55    inference(avatar_component_clause,[],[f1242])).
% 1.38/0.55  fof(f1242,plain,(
% 1.38/0.55    spl12_10 <=> r2_hidden(sK5(k1_tarski(sK0),sK0),sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.38/0.55  fof(f1771,plain,(
% 1.38/0.55    ~spl12_14 | ~spl12_10 | ~spl12_7),
% 1.38/0.55    inference(avatar_split_clause,[],[f940,f844,f1242,f1768])).
% 1.38/0.55  fof(f844,plain,(
% 1.38/0.55    spl12_7 <=> ! [X1] : (sK0 != X1 | ~r2_hidden(sK5(k1_tarski(sK0),X1),X1) | ~r2_hidden(sK5(k1_tarski(sK0),X1),sK7(k1_tarski(sK0),X1)))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.38/0.55  fof(f940,plain,(
% 1.38/0.55    ~r2_hidden(sK5(k1_tarski(sK0),sK0),sK0) | ~r2_hidden(sK5(k1_tarski(sK0),sK0),sK7(k1_tarski(sK0),sK0)) | ~spl12_7),
% 1.38/0.55    inference(equality_resolution,[],[f845])).
% 1.38/0.55  fof(f845,plain,(
% 1.38/0.55    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK5(k1_tarski(sK0),X1),X1) | ~r2_hidden(sK5(k1_tarski(sK0),X1),sK7(k1_tarski(sK0),X1))) ) | ~spl12_7),
% 1.38/0.55    inference(avatar_component_clause,[],[f844])).
% 1.38/0.55  fof(f1721,plain,(
% 1.38/0.55    spl12_10 | ~spl12_13),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f1713])).
% 1.38/0.55  fof(f1713,plain,(
% 1.38/0.55    $false | (spl12_10 | ~spl12_13)),
% 1.38/0.55    inference(resolution,[],[f1682,f128])).
% 1.38/0.55  fof(f128,plain,(
% 1.38/0.55    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.38/0.55    inference(equality_resolution,[],[f127])).
% 1.38/0.55  fof(f127,plain,(
% 1.38/0.55    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.38/0.55    inference(equality_resolution,[],[f95])).
% 1.38/0.55  fof(f95,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.38/0.55    inference(cnf_transformation,[],[f13])).
% 1.38/0.55  fof(f1682,plain,(
% 1.38/0.55    ~r2_hidden(sK0,k1_tarski(sK0)) | (spl12_10 | ~spl12_13)),
% 1.38/0.55    inference(resolution,[],[f1579,f1244])).
% 1.38/0.55  fof(f1244,plain,(
% 1.38/0.55    ~r2_hidden(sK5(k1_tarski(sK0),sK0),sK0) | spl12_10),
% 1.38/0.55    inference(avatar_component_clause,[],[f1242])).
% 1.38/0.55  fof(f1579,plain,(
% 1.38/0.55    ( ! [X0] : (r2_hidden(sK5(k1_tarski(sK0),sK0),X0) | ~r2_hidden(X0,k1_tarski(sK0))) ) | ~spl12_13),
% 1.38/0.55    inference(avatar_component_clause,[],[f1578])).
% 1.38/0.55  fof(f1578,plain,(
% 1.38/0.55    spl12_13 <=> ! [X0] : (r2_hidden(sK5(k1_tarski(sK0),sK0),X0) | ~r2_hidden(X0,k1_tarski(sK0)))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 1.38/0.55  fof(f1580,plain,(
% 1.38/0.55    spl12_13 | spl12_10 | ~spl12_8),
% 1.38/0.55    inference(avatar_split_clause,[],[f1026,f1000,f1242,f1578])).
% 1.38/0.55  fof(f1000,plain,(
% 1.38/0.55    spl12_8 <=> ! [X3,X2] : (sK0 != X2 | r2_hidden(sK5(k1_tarski(sK0),X2),X2) | r2_hidden(sK5(k1_tarski(sK0),X2),X3) | ~r2_hidden(X3,k1_tarski(sK0)))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.38/0.55  fof(f1026,plain,(
% 1.38/0.55    ( ! [X0] : (r2_hidden(sK5(k1_tarski(sK0),sK0),sK0) | r2_hidden(sK5(k1_tarski(sK0),sK0),X0) | ~r2_hidden(X0,k1_tarski(sK0))) ) | ~spl12_8),
% 1.38/0.55    inference(equality_resolution,[],[f1001])).
% 1.38/0.55  fof(f1001,plain,(
% 1.38/0.55    ( ! [X2,X3] : (sK0 != X2 | r2_hidden(sK5(k1_tarski(sK0),X2),X2) | r2_hidden(sK5(k1_tarski(sK0),X2),X3) | ~r2_hidden(X3,k1_tarski(sK0))) ) | ~spl12_8),
% 1.38/0.55    inference(avatar_component_clause,[],[f1000])).
% 1.38/0.55  fof(f1245,plain,(
% 1.38/0.55    spl12_9 | ~spl12_10 | ~spl12_4),
% 1.38/0.55    inference(avatar_split_clause,[],[f716,f199,f1242,f1238])).
% 1.38/0.55  fof(f199,plain,(
% 1.38/0.55    spl12_4 <=> ! [X0] : (sK0 != X0 | ~r2_hidden(sK5(k1_tarski(sK0),X0),X0) | r2_hidden(sK7(k1_tarski(sK0),X0),k1_tarski(sK0)))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.38/0.55  fof(f716,plain,(
% 1.38/0.55    ~r2_hidden(sK5(k1_tarski(sK0),sK0),sK0) | r2_hidden(sK7(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~spl12_4),
% 1.38/0.55    inference(equality_resolution,[],[f200])).
% 1.38/0.55  fof(f200,plain,(
% 1.38/0.55    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK5(k1_tarski(sK0),X0),X0) | r2_hidden(sK7(k1_tarski(sK0),X0),k1_tarski(sK0))) ) | ~spl12_4),
% 1.38/0.55    inference(avatar_component_clause,[],[f199])).
% 1.38/0.55  fof(f1002,plain,(
% 1.38/0.55    spl12_3 | spl12_8),
% 1.38/0.55    inference(avatar_split_clause,[],[f139,f1000,f195])).
% 1.38/0.55  fof(f195,plain,(
% 1.38/0.55    spl12_3 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.38/0.55  fof(f139,plain,(
% 1.38/0.55    ( ! [X2,X3] : (sK0 != X2 | k1_xboole_0 = k1_tarski(sK0) | ~r2_hidden(X3,k1_tarski(sK0)) | r2_hidden(sK5(k1_tarski(sK0),X2),X3) | r2_hidden(sK5(k1_tarski(sK0),X2),X2)) )),
% 1.38/0.55    inference(superposition,[],[f52,f76])).
% 1.38/0.55  fof(f76,plain,(
% 1.38/0.55    ( ! [X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(sK5(X0,X1),X3) | r2_hidden(sK5(X0,X1),X1) | k1_setfam_1(X0) = X1) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f40,plain,(
% 1.38/0.55    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f26])).
% 1.38/0.55  fof(f26,axiom,(
% 1.38/0.55    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.38/0.55  fof(f52,plain,(
% 1.38/0.55    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.38/0.55    inference(cnf_transformation,[],[f35])).
% 1.38/0.55  fof(f35,plain,(
% 1.38/0.55    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.38/0.55    inference(ennf_transformation,[],[f33])).
% 1.38/0.55  fof(f33,negated_conjecture,(
% 1.38/0.55    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.38/0.55    inference(negated_conjecture,[],[f32])).
% 1.38/0.55  fof(f32,conjecture,(
% 1.38/0.55    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.38/0.55  fof(f846,plain,(
% 1.38/0.55    spl12_3 | spl12_7),
% 1.38/0.55    inference(avatar_split_clause,[],[f138,f844,f195])).
% 1.38/0.55  fof(f138,plain,(
% 1.38/0.55    ( ! [X1] : (sK0 != X1 | k1_xboole_0 = k1_tarski(sK0) | ~r2_hidden(sK5(k1_tarski(sK0),X1),sK7(k1_tarski(sK0),X1)) | ~r2_hidden(sK5(k1_tarski(sK0),X1),X1)) )),
% 1.38/0.55    inference(superposition,[],[f52,f75])).
% 1.38/0.55  fof(f75,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK5(X0,X1),sK7(X0,X1)) | ~r2_hidden(sK5(X0,X1),X1) | k1_setfam_1(X0) = X1) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f290,plain,(
% 1.38/0.55    spl12_2 | ~spl12_3),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f284])).
% 1.38/0.55  fof(f284,plain,(
% 1.38/0.55    $false | (spl12_2 | ~spl12_3)),
% 1.38/0.55    inference(subsumption_resolution,[],[f150,f253])).
% 1.38/0.55  fof(f253,plain,(
% 1.38/0.55    k1_xboole_0 = sK0 | ~spl12_3),
% 1.38/0.55    inference(forward_demodulation,[],[f235,f54])).
% 1.38/0.55  fof(f54,plain,(
% 1.38/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.38/0.55    inference(cnf_transformation,[],[f19])).
% 1.38/0.55  fof(f19,axiom,(
% 1.38/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.38/0.55  fof(f235,plain,(
% 1.38/0.55    k3_tarski(k1_xboole_0) = sK0 | ~spl12_3),
% 1.38/0.55    inference(superposition,[],[f57,f197])).
% 1.38/0.55  fof(f197,plain,(
% 1.38/0.55    k1_xboole_0 = k1_tarski(sK0) | ~spl12_3),
% 1.38/0.55    inference(avatar_component_clause,[],[f195])).
% 1.38/0.55  fof(f57,plain,(
% 1.38/0.55    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f20,axiom,(
% 1.38/0.55    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.38/0.55  fof(f150,plain,(
% 1.38/0.55    k1_xboole_0 != sK0 | spl12_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f148])).
% 1.38/0.55  fof(f148,plain,(
% 1.38/0.55    spl12_2 <=> k1_xboole_0 = sK0),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.38/0.55  fof(f201,plain,(
% 1.38/0.55    spl12_3 | spl12_4),
% 1.38/0.55    inference(avatar_split_clause,[],[f137,f199,f195])).
% 1.38/0.55  fof(f137,plain,(
% 1.38/0.55    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK7(k1_tarski(sK0),X0),k1_tarski(sK0)) | ~r2_hidden(sK5(k1_tarski(sK0),X0),X0)) )),
% 1.38/0.55    inference(superposition,[],[f52,f74])).
% 1.38/0.55  fof(f74,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | r2_hidden(sK7(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1) | k1_setfam_1(X0) = X1) )),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f172,plain,(
% 1.38/0.55    spl12_1),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f152])).
% 1.38/0.55  fof(f152,plain,(
% 1.38/0.55    $false | spl12_1),
% 1.38/0.55    inference(resolution,[],[f146,f128])).
% 1.38/0.55  fof(f146,plain,(
% 1.38/0.55    ~r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) | spl12_1),
% 1.38/0.55    inference(avatar_component_clause,[],[f144])).
% 1.38/0.55  fof(f144,plain,(
% 1.38/0.55    spl12_1 <=> r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.38/0.55  fof(f151,plain,(
% 1.38/0.55    ~spl12_1 | ~spl12_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f142,f148,f144])).
% 1.38/0.55  fof(f142,plain,(
% 1.38/0.55    k1_xboole_0 != sK0 | ~r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))),
% 1.38/0.55    inference(inner_rewriting,[],[f140])).
% 1.38/0.55  fof(f140,plain,(
% 1.38/0.55    k1_xboole_0 != sK0 | ~r2_hidden(k1_xboole_0,k1_tarski(sK0))),
% 1.38/0.55    inference(superposition,[],[f52,f62])).
% 1.38/0.55  fof(f62,plain,(
% 1.38/0.55    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k1_setfam_1(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f37])).
% 1.38/0.55  fof(f37,plain,(
% 1.38/0.55    ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | ~r2_hidden(k1_xboole_0,X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f29])).
% 1.38/0.55  fof(f29,axiom,(
% 1.38/0.55    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (3802)------------------------------
% 1.38/0.55  % (3802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (3802)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (3802)Memory used [KB]: 11257
% 1.38/0.55  % (3802)Time elapsed: 0.130 s
% 1.38/0.55  % (3802)------------------------------
% 1.38/0.55  % (3802)------------------------------
% 1.38/0.55  % (3803)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.38/0.55  % (3781)Success in time 0.197 s
%------------------------------------------------------------------------------
