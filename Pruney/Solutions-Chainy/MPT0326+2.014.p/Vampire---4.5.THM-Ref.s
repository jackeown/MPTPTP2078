%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 110 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 281 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f687,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f172,f195,f208,f228,f502,f517,f550,f564,f644,f686])).

fof(f686,plain,(
    ~ spl4_47 ),
    inference(avatar_contradiction_clause,[],[f668])).

fof(f668,plain,
    ( $false
    | ~ spl4_47 ),
    inference(resolution,[],[f650,f20])).

fof(f20,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f650,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl4_47 ),
    inference(resolution,[],[f563,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f563,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))
        | r1_tarski(sK1,X0) )
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl4_47
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f644,plain,(
    ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | ~ spl4_18 ),
    inference(resolution,[],[f620,f20])).

fof(f620,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl4_18 ),
    inference(resolution,[],[f129,f23])).

fof(f129,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2))
        | r1_tarski(sK1,X2) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_18
  <=> ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2))
        | r1_tarski(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f564,plain,
    ( spl4_17
    | spl4_47
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f553,f140,f562,f125])).

fof(f125,plain,
    ( spl4_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f140,plain,
    ( spl4_20
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f553,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))
        | k1_xboole_0 = sK0
        | r1_tarski(sK1,X0) )
    | ~ spl4_20 ),
    inference(superposition,[],[f27,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f140])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f550,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | spl4_32 ),
    inference(resolution,[],[f430,f23])).

fof(f430,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl4_32
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f517,plain,
    ( spl4_13
    | spl4_20
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f505,f32,f140,f99])).

fof(f99,plain,
    ( spl4_13
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f32,plain,
    ( spl4_1
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f505,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | r1_tarski(sK1,sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f33,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f502,plain,
    ( spl4_3
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f239,f429,f50])).

fof(f50,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f239,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f45,f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ r1_tarski(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f228,plain,
    ( spl4_17
    | spl4_18
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f220,f80,f128,f125])).

fof(f80,plain,
    ( spl4_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f220,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2))
        | k1_xboole_0 = sK0
        | r1_tarski(sK1,X2) )
    | ~ spl4_9 ),
    inference(superposition,[],[f28,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f208,plain,
    ( spl4_13
    | spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f204,f35,f80,f99])).

fof(f35,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f204,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f195,plain,
    ( ~ spl4_3
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(resolution,[],[f193,f51])).

fof(f51,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f193,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f21,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f125])).

fof(f21,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f172,plain,(
    ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl4_13 ),
    inference(resolution,[],[f100,f20])).

fof(f100,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f37,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f19,f35,f32])).

fof(f19,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:58:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.49  % (1364)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.23/0.51  % (1354)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.51  % (1354)Refutation not found, incomplete strategy% (1354)------------------------------
% 0.23/0.51  % (1354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (1354)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (1354)Memory used [KB]: 10490
% 0.23/0.51  % (1354)Time elapsed: 0.090 s
% 0.23/0.51  % (1354)------------------------------
% 0.23/0.51  % (1354)------------------------------
% 0.23/0.51  % (1356)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.51  % (1364)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f687,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f37,f172,f195,f208,f228,f502,f517,f550,f564,f644,f686])).
% 0.23/0.51  fof(f686,plain,(
% 0.23/0.51    ~spl4_47),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f668])).
% 0.23/0.51  fof(f668,plain,(
% 0.23/0.51    $false | ~spl4_47),
% 0.23/0.51    inference(resolution,[],[f650,f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ~r1_tarski(sK1,sK3)),
% 0.23/0.51    inference(cnf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,plain,(
% 0.23/0.51    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,negated_conjecture,(
% 0.23/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.23/0.51    inference(negated_conjecture,[],[f8])).
% 0.23/0.51  fof(f8,conjecture,(
% 0.23/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.23/0.51  fof(f650,plain,(
% 0.23/0.51    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl4_47),
% 0.23/0.51    inference(resolution,[],[f563,f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.51  fof(f563,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0)) | r1_tarski(sK1,X0)) ) | ~spl4_47),
% 0.23/0.51    inference(avatar_component_clause,[],[f562])).
% 0.23/0.51  fof(f562,plain,(
% 0.23/0.51    spl4_47 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0)) | r1_tarski(sK1,X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.23/0.51  fof(f644,plain,(
% 0.23/0.51    ~spl4_18),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f626])).
% 0.23/0.51  fof(f626,plain,(
% 0.23/0.51    $false | ~spl4_18),
% 0.23/0.51    inference(resolution,[],[f620,f20])).
% 0.23/0.51  fof(f620,plain,(
% 0.23/0.51    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl4_18),
% 0.23/0.51    inference(resolution,[],[f129,f23])).
% 0.23/0.51  fof(f129,plain,(
% 0.23/0.51    ( ! [X2] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2)) | r1_tarski(sK1,X2)) ) | ~spl4_18),
% 0.23/0.51    inference(avatar_component_clause,[],[f128])).
% 0.23/0.51  fof(f128,plain,(
% 0.23/0.51    spl4_18 <=> ! [X2] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2)) | r1_tarski(sK1,X2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.23/0.51  fof(f564,plain,(
% 0.23/0.51    spl4_17 | spl4_47 | ~spl4_20),
% 0.23/0.51    inference(avatar_split_clause,[],[f553,f140,f562,f125])).
% 0.23/0.51  fof(f125,plain,(
% 0.23/0.51    spl4_17 <=> k1_xboole_0 = sK0),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.23/0.51  fof(f140,plain,(
% 0.23/0.51    spl4_20 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.23/0.51  fof(f553,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0)) | k1_xboole_0 = sK0 | r1_tarski(sK1,X0)) ) | ~spl4_20),
% 0.23/0.51    inference(superposition,[],[f27,f141])).
% 0.23/0.51  fof(f141,plain,(
% 0.23/0.51    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl4_20),
% 0.23/0.51    inference(avatar_component_clause,[],[f140])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.23/0.51  fof(f550,plain,(
% 0.23/0.51    spl4_32),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f544])).
% 0.23/0.51  fof(f544,plain,(
% 0.23/0.51    $false | spl4_32),
% 0.23/0.51    inference(resolution,[],[f430,f23])).
% 0.23/0.51  fof(f430,plain,(
% 0.23/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_32),
% 0.23/0.51    inference(avatar_component_clause,[],[f429])).
% 0.23/0.51  fof(f429,plain,(
% 0.23/0.51    spl4_32 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.23/0.51  fof(f517,plain,(
% 0.23/0.51    spl4_13 | spl4_20 | ~spl4_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f505,f32,f140,f99])).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    spl4_13 <=> r1_tarski(sK1,sK3)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    spl4_1 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.51  fof(f505,plain,(
% 0.23/0.51    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | r1_tarski(sK1,sK3) | ~spl4_1),
% 0.23/0.51    inference(resolution,[],[f33,f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.23/0.51    inference(flattening,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl4_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f32])).
% 0.23/0.51  fof(f502,plain,(
% 0.23/0.51    spl4_3 | ~spl4_32),
% 0.23/0.51    inference(avatar_split_clause,[],[f239,f429,f50])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.51  fof(f239,plain,(
% 0.23/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0)),
% 0.23/0.51    inference(resolution,[],[f45,f23])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r1_tarski(X0,X1) | v1_xboole_0(X0)) )),
% 0.23/0.51    inference(resolution,[],[f25,f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | ~r1_xboole_0(X0,X1) | v1_xboole_0(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.23/0.51    inference(flattening,[],[f12])).
% 0.23/0.51  fof(f12,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.23/0.51  fof(f228,plain,(
% 0.23/0.51    spl4_17 | spl4_18 | ~spl4_9),
% 0.23/0.51    inference(avatar_split_clause,[],[f220,f80,f128,f125])).
% 0.23/0.51  fof(f80,plain,(
% 0.23/0.51    spl4_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.23/0.51  fof(f220,plain,(
% 0.23/0.51    ( ! [X2] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X2)) | k1_xboole_0 = sK0 | r1_tarski(sK1,X2)) ) | ~spl4_9),
% 0.23/0.51    inference(superposition,[],[f28,f81])).
% 0.23/0.51  fof(f81,plain,(
% 0.23/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_9),
% 0.23/0.51    inference(avatar_component_clause,[],[f80])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f208,plain,(
% 0.23/0.51    spl4_13 | spl4_9 | ~spl4_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f204,f35,f80,f99])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    spl4_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.51  fof(f204,plain,(
% 0.23/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK1,sK3) | ~spl4_2),
% 0.23/0.51    inference(resolution,[],[f36,f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f35])).
% 0.23/0.51  fof(f195,plain,(
% 0.23/0.51    ~spl4_3 | ~spl4_17),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f194])).
% 0.23/0.51  fof(f194,plain,(
% 0.23/0.51    $false | (~spl4_3 | ~spl4_17)),
% 0.23/0.51    inference(resolution,[],[f193,f51])).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f50])).
% 0.23/0.51  fof(f193,plain,(
% 0.23/0.51    ~v1_xboole_0(k1_xboole_0) | ~spl4_17),
% 0.23/0.51    inference(backward_demodulation,[],[f21,f126])).
% 0.23/0.51  fof(f126,plain,(
% 0.23/0.51    k1_xboole_0 = sK0 | ~spl4_17),
% 0.23/0.51    inference(avatar_component_clause,[],[f125])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ~v1_xboole_0(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f10])).
% 0.23/0.51  fof(f172,plain,(
% 0.23/0.51    ~spl4_13),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f167])).
% 0.23/0.51  fof(f167,plain,(
% 0.23/0.51    $false | ~spl4_13),
% 0.23/0.51    inference(resolution,[],[f100,f20])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    r1_tarski(sK1,sK3) | ~spl4_13),
% 0.23/0.51    inference(avatar_component_clause,[],[f99])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    spl4_1 | spl4_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f19,f35,f32])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.23/0.51    inference(cnf_transformation,[],[f10])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (1364)------------------------------
% 0.23/0.51  % (1364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (1364)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (1364)Memory used [KB]: 11001
% 0.23/0.51  % (1364)Time elapsed: 0.054 s
% 0.23/0.51  % (1364)------------------------------
% 0.23/0.51  % (1364)------------------------------
% 0.23/0.51  % (1370)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.23/0.52  % (1350)Success in time 0.147 s
%------------------------------------------------------------------------------
