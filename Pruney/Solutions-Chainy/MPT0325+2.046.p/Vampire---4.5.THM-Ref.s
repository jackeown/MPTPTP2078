%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
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
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f44,f124,f131,f151,f173,f196,f208,f211,f216,f224,f227])).

fof(f227,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl5_17 ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_17 ),
    inference(superposition,[],[f223,f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f223,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl5_17
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f224,plain,
    ( ~ spl5_17
    | spl5_1
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f218,f135,f27,f221])).

fof(f27,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f135,plain,
    ( spl5_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f218,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl5_1
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f29,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f29,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f216,plain,
    ( spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f214,f119,f135])).

fof(f119,plain,
    ( spl5_10
  <=> ! [X1] : r1_tarski(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f214,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_10 ),
    inference(resolution,[],[f120,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f120,plain,
    ( ! [X1] : r1_tarski(sK0,X1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f211,plain,
    ( spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f209,f126,f41])).

fof(f41,plain,
    ( spl5_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f126,plain,
    ( spl5_12
  <=> ! [X3] :
        ( r1_tarski(sK0,X3)
        | r2_hidden(sK4(sK0,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f209,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f127,f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK0,X3),sK2)
        | r1_tarski(sK0,X3) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f208,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl5_16 ),
    inference(trivial_inequality_removal,[],[f206])).

fof(f206,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_16 ),
    inference(superposition,[],[f195,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f195,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_16
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f196,plain,
    ( ~ spl5_16
    | spl5_1
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f182,f170,f27,f193])).

fof(f170,plain,
    ( spl5_15
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f182,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl5_1
    | ~ spl5_15 ),
    inference(backward_demodulation,[],[f29,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f173,plain,
    ( spl5_15
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f167,f129,f170])).

fof(f129,plain,
    ( spl5_13
  <=> ! [X2] : r1_tarski(sK1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f167,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_13 ),
    inference(resolution,[],[f130,f14])).

fof(f130,plain,
    ( ! [X2] : r1_tarski(sK1,X2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f151,plain,
    ( spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f150,f122,f37])).

fof(f37,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f122,plain,
    ( spl5_11
  <=> ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK4(sK1,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f150,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl5_11 ),
    inference(resolution,[],[f123,f17])).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),sK3)
        | r1_tarski(sK1,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f131,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f114,f32,f129,f126])).

fof(f32,plain,
    ( spl5_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f114,plain,
    ( ! [X2,X3] :
        ( r1_tarski(sK1,X2)
        | r1_tarski(sK0,X3)
        | r2_hidden(sK4(sK0,X3),sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

% (32166)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f109,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(sK0,X1),sK4(sK1,X0)),k2_zfmisc_1(sK2,sK3))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK0,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f67,f34])).

fof(f34,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f67,plain,(
    ! [X24,X23,X21,X22,X20] :
      ( ~ r1_tarski(k2_zfmisc_1(X20,X22),X24)
      | r1_tarski(X22,X23)
      | r2_hidden(k4_tarski(sK4(X20,X21),sK4(X22,X23)),X24)
      | r1_tarski(X20,X21) ) ),
    inference(resolution,[],[f61,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK4(X2,X3)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X0,X1)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f54,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
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

fof(f124,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f113,f32,f122,f119])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1,X0)
        | r1_tarski(sK0,X1)
        | r2_hidden(sK4(sK1,X0),sK3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:25:25 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (32161)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (32177)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (32161)Refutation not found, incomplete strategy% (32161)------------------------------
% 0.21/0.51  % (32161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32161)Memory used [KB]: 1663
% 0.21/0.51  % (32161)Time elapsed: 0.102 s
% 0.21/0.51  % (32161)------------------------------
% 0.21/0.51  % (32161)------------------------------
% 0.21/0.51  % (32170)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (32169)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (32163)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (32176)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (32165)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (32177)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (32184)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f30,f35,f44,f124,f131,f151,f173,f196,f208,f211,f216,f224,f227])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    spl5_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f226])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    $false | spl5_17),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f225])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | spl5_17),
% 0.21/0.52    inference(superposition,[],[f223,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f221])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    spl5_17 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    ~spl5_17 | spl5_1 | ~spl5_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f218,f135,f27,f221])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    spl5_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl5_14 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl5_1 | ~spl5_14)),
% 0.21/0.52    inference(backward_demodulation,[],[f29,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f27])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    spl5_14 | ~spl5_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f214,f119,f135])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl5_10 <=> ! [X1] : r1_tarski(sK0,X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl5_10),
% 0.21/0.52    inference(resolution,[],[f120,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(sK0,X1)) ) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f119])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    spl5_4 | ~spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f209,f126,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl5_4 <=> r1_tarski(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl5_12 <=> ! [X3] : (r1_tarski(sK0,X3) | r2_hidden(sK4(sK0,X3),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    r1_tarski(sK0,sK2) | ~spl5_12),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl5_12),
% 0.21/0.52    inference(resolution,[],[f127,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(sK4(sK0,X3),sK2) | r1_tarski(sK0,X3)) ) | ~spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    spl5_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    $false | spl5_16),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f206])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | spl5_16),
% 0.21/0.52    inference(superposition,[],[f195,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl5_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f193])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl5_16 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ~spl5_16 | spl5_1 | ~spl5_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f182,f170,f27,f193])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl5_15 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl5_1 | ~spl5_15)),
% 0.21/0.52    inference(backward_demodulation,[],[f29,f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl5_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f170])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    spl5_15 | ~spl5_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f167,f129,f170])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl5_13 <=> ! [X2] : r1_tarski(sK1,X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl5_13),
% 0.21/0.52    inference(resolution,[],[f130,f14])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X2] : (r1_tarski(sK1,X2)) ) | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl5_3 | ~spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f150,f122,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    spl5_3 <=> r1_tarski(sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl5_11 <=> ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,X0),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    r1_tarski(sK1,sK3) | ~spl5_11),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl5_11),
% 0.21/0.52    inference(resolution,[],[f123,f17])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK3) | r1_tarski(sK1,X0)) ) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl5_12 | spl5_13 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f32,f129,f126])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    spl5_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_tarski(sK1,X2) | r1_tarski(sK0,X3) | r2_hidden(sK4(sK0,X3),sK2)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f109,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  % (32166)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(sK0,X1),sK4(sK1,X0)),k2_zfmisc_1(sK2,sK3)) | r1_tarski(sK1,X0) | r1_tarski(sK0,X1)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f67,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f32])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X24,X23,X21,X22,X20] : (~r1_tarski(k2_zfmisc_1(X20,X22),X24) | r1_tarski(X22,X23) | r2_hidden(k4_tarski(sK4(X20,X21),sK4(X22,X23)),X24) | r1_tarski(X20,X21)) )),
% 0.21/0.52    inference(resolution,[],[f61,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK4(X2,X3)),k2_zfmisc_1(X0,X2)) | r1_tarski(X0,X1) | r1_tarski(X2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f54,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK4(X2,X3),X0),k2_zfmisc_1(X2,X1)) | r1_tarski(X2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f23,f16])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl5_10 | spl5_11 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f113,f32,f122,f119])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(sK1,X0) | r1_tarski(sK0,X1) | r2_hidden(sK4(sK1,X0),sK3)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f109,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~spl5_3 | ~spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f11,f41,f37])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f12,f32])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f13,f27])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (32177)------------------------------
% 0.21/0.52  % (32177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32177)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (32177)Memory used [KB]: 10874
% 0.21/0.52  % (32177)Time elapsed: 0.122 s
% 0.21/0.52  % (32177)------------------------------
% 0.21/0.52  % (32177)------------------------------
% 0.21/0.53  % (32168)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (32160)Success in time 0.166 s
%------------------------------------------------------------------------------
