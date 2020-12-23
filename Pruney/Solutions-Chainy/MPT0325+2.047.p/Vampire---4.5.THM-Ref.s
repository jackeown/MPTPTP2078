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
% DateTime   : Thu Dec  3 12:42:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 143 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  183 ( 359 expanded)
%              Number of equality atoms :   33 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f44,f125,f132,f152,f174,f197,f209,f212,f217,f225,f228])).

fof(f228,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl5_17 ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_17 ),
    inference(superposition,[],[f224,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f224,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl5_17
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f225,plain,
    ( ~ spl5_17
    | spl5_1
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f219,f136,f27,f222])).

fof(f27,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f136,plain,
    ( spl5_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f219,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl5_1
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f29,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f29,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f217,plain,
    ( spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f215,f120,f136])).

fof(f120,plain,
    ( spl5_10
  <=> ! [X1] : r1_tarski(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f215,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_10 ),
    inference(resolution,[],[f121,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f121,plain,
    ( ! [X1] : r1_tarski(sK0,X1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f212,plain,
    ( spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f210,f127,f41])).

fof(f41,plain,
    ( spl5_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f127,plain,
    ( spl5_12
  <=> ! [X3] :
        ( r1_tarski(sK0,X3)
        | r2_hidden(sK4(sK0,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f210,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f128,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f128,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK0,X3),sK2)
        | r1_tarski(sK0,X3) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f209,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl5_16 ),
    inference(trivial_inequality_removal,[],[f207])).

fof(f207,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_16 ),
    inference(superposition,[],[f196,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f196,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl5_16
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f197,plain,
    ( ~ spl5_16
    | spl5_1
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f183,f171,f27,f194])).

fof(f171,plain,
    ( spl5_15
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f183,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl5_1
    | ~ spl5_15 ),
    inference(backward_demodulation,[],[f29,f173])).

fof(f173,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( spl5_15
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f168,f130,f171])).

fof(f130,plain,
    ( spl5_13
  <=> ! [X2] : r1_tarski(sK1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f168,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_13 ),
    inference(resolution,[],[f131,f14])).

fof(f131,plain,
    ( ! [X2] : r1_tarski(sK1,X2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f152,plain,
    ( spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f151,f123,f37])).

fof(f37,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f123,plain,
    ( spl5_11
  <=> ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK4(sK1,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f151,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl5_11 ),
    inference(resolution,[],[f124,f17])).

fof(f124,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),sK3)
        | r1_tarski(sK1,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f132,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f115,f32,f130,f127])).

fof(f32,plain,
    ( spl5_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f115,plain,
    ( ! [X2,X3] :
        ( r1_tarski(sK1,X2)
        | r1_tarski(sK0,X3)
        | r2_hidden(sK4(sK0,X3),sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f110,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f110,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(sK0,X1),sK4(sK1,X0)),k2_zfmisc_1(sK2,sK3))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK0,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f34])).

fof(f34,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f68,plain,(
    ! [X24,X23,X21,X22,X20] :
      ( ~ r1_tarski(k2_zfmisc_1(X20,X22),X24)
      | r1_tarski(X22,X23)
      | r2_hidden(k4_tarski(sK4(X20,X21),sK4(X22,X23)),X24)
      | r1_tarski(X20,X21) ) ),
    inference(resolution,[],[f62,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK4(X2,X3)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X0,X1)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f55,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

% (16385)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK4(X2,X3),X0),k2_zfmisc_1(X2,X1))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f23,f16])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f125,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f114,f32,f123,f120])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1,X0)
        | r1_tarski(sK0,X1)
        | r2_hidden(sK4(sK1,X0),sK3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f110,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f11,f41,f37])).

fof(f11,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f35,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f12,f32])).

fof(f12,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (16384)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (16381)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (16398)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (16376)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (16382)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (16373)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (16390)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (16377)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (16372)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (16388)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (16395)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (16372)Refutation not found, incomplete strategy% (16372)------------------------------
% 0.20/0.52  % (16372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16372)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16372)Memory used [KB]: 1663
% 0.20/0.52  % (16372)Time elapsed: 0.104 s
% 0.20/0.52  % (16372)------------------------------
% 0.20/0.52  % (16372)------------------------------
% 0.20/0.52  % (16394)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (16374)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (16395)Refutation not found, incomplete strategy% (16395)------------------------------
% 0.20/0.53  % (16395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16395)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16395)Memory used [KB]: 10618
% 0.20/0.53  % (16395)Time elapsed: 0.090 s
% 0.20/0.53  % (16395)------------------------------
% 0.20/0.53  % (16395)------------------------------
% 0.20/0.53  % (16386)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (16379)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (16390)Refutation not found, incomplete strategy% (16390)------------------------------
% 0.20/0.53  % (16390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16390)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16390)Memory used [KB]: 10618
% 0.20/0.53  % (16390)Time elapsed: 0.122 s
% 0.20/0.53  % (16390)------------------------------
% 0.20/0.53  % (16390)------------------------------
% 0.20/0.53  % (16378)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (16380)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (16401)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (16396)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (16375)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (16383)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (16387)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (16388)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (16374)Refutation not found, incomplete strategy% (16374)------------------------------
% 0.20/0.54  % (16374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16380)Refutation not found, incomplete strategy% (16380)------------------------------
% 0.20/0.54  % (16380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16380)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16380)Memory used [KB]: 10618
% 0.20/0.54  % (16380)Time elapsed: 0.140 s
% 0.20/0.54  % (16380)------------------------------
% 0.20/0.54  % (16380)------------------------------
% 0.20/0.54  % (16402)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (16374)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16374)Memory used [KB]: 10618
% 0.20/0.54  % (16374)Time elapsed: 0.137 s
% 0.20/0.54  % (16374)------------------------------
% 0.20/0.54  % (16374)------------------------------
% 0.20/0.54  % (16393)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (16400)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (16397)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (16392)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (16399)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (16391)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f30,f35,f44,f125,f132,f152,f174,f197,f209,f212,f217,f225,f228])).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    spl5_17),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f227])).
% 0.20/0.55  fof(f227,plain,(
% 0.20/0.55    $false | spl5_17),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f226])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | spl5_17),
% 0.20/0.55    inference(superposition,[],[f224,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl5_17),
% 0.20/0.55    inference(avatar_component_clause,[],[f222])).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    spl5_17 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.55  fof(f225,plain,(
% 0.20/0.55    ~spl5_17 | spl5_1 | ~spl5_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f219,f136,f27,f222])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    spl5_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    spl5_14 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl5_1 | ~spl5_14)),
% 0.20/0.55    inference(backward_demodulation,[],[f29,f138])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl5_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f136])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl5_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f27])).
% 0.20/0.55  fof(f217,plain,(
% 0.20/0.55    spl5_14 | ~spl5_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f215,f120,f136])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    spl5_10 <=> ! [X1] : r1_tarski(sK0,X1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl5_10),
% 0.20/0.55    inference(resolution,[],[f121,f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(sK0,X1)) ) | ~spl5_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f120])).
% 0.20/0.55  fof(f212,plain,(
% 0.20/0.55    spl5_4 | ~spl5_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f210,f127,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    spl5_4 <=> r1_tarski(sK0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    spl5_12 <=> ! [X3] : (r1_tarski(sK0,X3) | r2_hidden(sK4(sK0,X3),sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    r1_tarski(sK0,sK2) | ~spl5_12),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl5_12),
% 0.20/0.55    inference(resolution,[],[f128,f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    ( ! [X3] : (r2_hidden(sK4(sK0,X3),sK2) | r1_tarski(sK0,X3)) ) | ~spl5_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f127])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    spl5_16),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f208])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    $false | spl5_16),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f207])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | spl5_16),
% 0.20/0.55    inference(superposition,[],[f196,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl5_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f194])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    spl5_16 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    ~spl5_16 | spl5_1 | ~spl5_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f183,f171,f27,f194])).
% 0.20/0.55  fof(f171,plain,(
% 0.20/0.55    spl5_15 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.55  fof(f183,plain,(
% 0.20/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl5_1 | ~spl5_15)),
% 0.20/0.55    inference(backward_demodulation,[],[f29,f173])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl5_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f171])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    spl5_15 | ~spl5_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f168,f130,f171])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    spl5_13 <=> ! [X2] : r1_tarski(sK1,X2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl5_13),
% 0.20/0.55    inference(resolution,[],[f131,f14])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    ( ! [X2] : (r1_tarski(sK1,X2)) ) | ~spl5_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f130])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    spl5_3 | ~spl5_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f151,f123,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    spl5_3 <=> r1_tarski(sK1,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    spl5_11 <=> ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,X0),sK3))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.55  fof(f151,plain,(
% 0.20/0.55    r1_tarski(sK1,sK3) | ~spl5_11),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f146])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl5_11),
% 0.20/0.55    inference(resolution,[],[f124,f17])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK3) | r1_tarski(sK1,X0)) ) | ~spl5_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f123])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    spl5_12 | spl5_13 | ~spl5_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f115,f32,f130,f127])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    spl5_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ( ! [X2,X3] : (r1_tarski(sK1,X2) | r1_tarski(sK0,X3) | r2_hidden(sK4(sK0,X3),sK2)) ) | ~spl5_2),
% 0.20/0.55    inference(resolution,[],[f110,f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(sK0,X1),sK4(sK1,X0)),k2_zfmisc_1(sK2,sK3)) | r1_tarski(sK1,X0) | r1_tarski(sK0,X1)) ) | ~spl5_2),
% 0.20/0.55    inference(resolution,[],[f68,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl5_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f32])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X24,X23,X21,X22,X20] : (~r1_tarski(k2_zfmisc_1(X20,X22),X24) | r1_tarski(X22,X23) | r2_hidden(k4_tarski(sK4(X20,X21),sK4(X22,X23)),X24) | r1_tarski(X20,X21)) )),
% 0.20/0.55    inference(resolution,[],[f62,f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK4(X2,X3)),k2_zfmisc_1(X0,X2)) | r1_tarski(X0,X1) | r1_tarski(X2,X3)) )),
% 0.20/0.55    inference(resolution,[],[f55,f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  % (16385)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK4(X2,X3),X0),k2_zfmisc_1(X2,X1)) | r1_tarski(X2,X3)) )),
% 0.20/0.55    inference(resolution,[],[f23,f16])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    spl5_10 | spl5_11 | ~spl5_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f114,f32,f123,f120])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(sK1,X0) | r1_tarski(sK0,X1) | r2_hidden(sK4(sK1,X0),sK3)) ) | ~spl5_2),
% 0.20/0.55    inference(resolution,[],[f110,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ~spl5_3 | ~spl5_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f11,f41,f37])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.55    inference(flattening,[],[f7])).
% 0.20/0.55  fof(f7,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f5])).
% 0.20/0.55  fof(f5,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    spl5_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f12,f32])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ~spl5_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f13,f27])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (16388)------------------------------
% 0.20/0.55  % (16388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16388)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (16388)Memory used [KB]: 10874
% 0.20/0.55  % (16388)Time elapsed: 0.148 s
% 0.20/0.55  % (16388)------------------------------
% 0.20/0.55  % (16388)------------------------------
% 0.20/0.56  % (16371)Success in time 0.199 s
%------------------------------------------------------------------------------
