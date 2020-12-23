%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:02 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 197 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :    8
%              Number of atoms          :  216 ( 456 expanded)
%              Number of equality atoms :   47 ( 129 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f77,f95,f105,f112,f145,f154,f184,f193,f233,f238,f254,f255])).

% (19842)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f255,plain,
    ( sK1 != k4_xboole_0(sK1,sK1)
    | r1_tarski(sK1,sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f254,plain,
    ( ~ spl5_16
    | spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f239,f229,f50,f251])).

fof(f251,plain,
    ( spl5_16
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f50,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f229,plain,
    ( spl5_14
  <=> sK1 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f239,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK1)
    | ~ spl5_14 ),
    inference(superposition,[],[f231,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f231,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f229])).

fof(f238,plain,
    ( spl5_15
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f227,f72,f235])).

fof(f235,plain,
    ( spl5_15
  <=> r1_tarski(k4_xboole_0(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f72,plain,
    ( spl5_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f227,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f40,f209])).

fof(f209,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))
    | ~ spl5_5 ),
    inference(resolution,[],[f198,f40])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0 )
    | ~ spl5_5 ),
    inference(resolution,[],[f196,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f196,plain,
    ( ! [X3] : ~ r2_xboole_0(X3,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f73,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f73,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f233,plain,
    ( spl5_14
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f217,f72,f229])).

fof(f217,plain,
    ( sK1 = k4_xboole_0(sK1,sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f209,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f193,plain,
    ( ~ spl5_10
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl5_10
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f108,f183,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f183,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl5_13
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

% (19840)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f108,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_10
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f184,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f159,f142,f45,f181])).

fof(f45,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f142,plain,
    ( spl5_12
  <=> sK0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f159,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,sK0)
    | ~ spl5_12 ),
    inference(superposition,[],[f144,f33])).

fof(f144,plain,
    ( sK0 = k4_xboole_0(sK0,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f154,plain,
    ( spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f153,f110,f102])).

fof(f102,plain,
    ( spl5_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f110,plain,
    ( spl5_11
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f153,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl5_11 ),
    inference(resolution,[],[f147,f31])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f111,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f110])).

% (19842)Refutation not found, incomplete strategy% (19842)------------------------------
% (19842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19842)Termination reason: Refutation not found, incomplete strategy

% (19842)Memory used [KB]: 6140
% (19842)Time elapsed: 0.114 s
% (19842)------------------------------
% (19842)------------------------------
fof(f145,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f129,f107,f142])).

fof(f129,plain,
    ( sK0 = k4_xboole_0(sK0,sK0)
    | ~ spl5_10 ),
    inference(superposition,[],[f124,f124])).

fof(f124,plain,
    ( ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
    | ~ spl5_10 ),
    inference(resolution,[],[f116,f40])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | sK0 = X0 )
    | ~ spl5_10 ),
    inference(resolution,[],[f115,f29])).

fof(f115,plain,
    ( ! [X3] : ~ r2_xboole_0(X3,sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f108,f35])).

fof(f112,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f69,f60,f110,f107])).

fof(f60,plain,
    ( spl5_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f65,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f65,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl5_4 ),
    inference(superposition,[],[f38,f62])).

fof(f62,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,
    ( ~ spl5_9
    | spl5_3
    | spl5_8 ),
    inference(avatar_split_clause,[],[f100,f92,f55,f102])).

fof(f55,plain,
    ( spl5_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( spl5_8
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f100,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | spl5_8 ),
    inference(resolution,[],[f94,f29])).

fof(f94,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f95,plain,
    ( ~ spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f90,f75,f92])).

fof(f75,plain,
    ( spl5_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f90,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ r2_xboole_0(sK1,sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f79,f35])).

fof(f79,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK1,X1),sK0)
        | ~ r2_xboole_0(sK1,X1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f67,f60,f75,f72])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f64,f39])).

% (19841)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl5_4 ),
    inference(superposition,[],[f37,f62])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f18,f60])).

fof(f18,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f58,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (19844)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.52  % (19860)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.52  % (19852)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.53  % (19860)Refutation found. Thanks to Tanya!
% 1.21/0.53  % SZS status Theorem for theBenchmark
% 1.21/0.53  % (19843)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.54  % (19865)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.21/0.54  % SZS output start Proof for theBenchmark
% 1.21/0.54  fof(f256,plain,(
% 1.21/0.54    $false),
% 1.21/0.54    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f77,f95,f105,f112,f145,f154,f184,f193,f233,f238,f254,f255])).
% 1.39/0.54  % (19842)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.54  fof(f255,plain,(
% 1.39/0.54    sK1 != k4_xboole_0(sK1,sK1) | r1_tarski(sK1,sK1) | ~r1_tarski(k4_xboole_0(sK1,sK1),sK1)),
% 1.39/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.54  fof(f254,plain,(
% 1.39/0.54    ~spl5_16 | spl5_2 | ~spl5_14),
% 1.39/0.54    inference(avatar_split_clause,[],[f239,f229,f50,f251])).
% 1.39/0.54  fof(f251,plain,(
% 1.39/0.54    spl5_16 <=> r1_tarski(sK1,sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.39/0.54  fof(f50,plain,(
% 1.39/0.54    spl5_2 <=> k1_xboole_0 = sK1),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.39/0.54  fof(f229,plain,(
% 1.39/0.54    spl5_14 <=> sK1 = k4_xboole_0(sK1,sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.39/0.54  fof(f239,plain,(
% 1.39/0.54    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK1) | ~spl5_14),
% 1.39/0.54    inference(superposition,[],[f231,f33])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.39/0.54  fof(f231,plain,(
% 1.39/0.54    sK1 = k4_xboole_0(sK1,sK1) | ~spl5_14),
% 1.39/0.54    inference(avatar_component_clause,[],[f229])).
% 1.39/0.54  fof(f238,plain,(
% 1.39/0.54    spl5_15 | ~spl5_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f227,f72,f235])).
% 1.39/0.54  fof(f235,plain,(
% 1.39/0.54    spl5_15 <=> r1_tarski(k4_xboole_0(sK1,sK1),sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.39/0.54  fof(f72,plain,(
% 1.39/0.54    spl5_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.39/0.54  fof(f227,plain,(
% 1.39/0.54    r1_tarski(k4_xboole_0(sK1,sK1),sK1) | ~spl5_5),
% 1.39/0.54    inference(superposition,[],[f40,f209])).
% 1.39/0.54  fof(f209,plain,(
% 1.39/0.54    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) ) | ~spl5_5),
% 1.39/0.54    inference(resolution,[],[f198,f40])).
% 1.39/0.54  fof(f198,plain,(
% 1.39/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0) ) | ~spl5_5),
% 1.39/0.54    inference(resolution,[],[f196,f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f2])).
% 1.39/0.54  fof(f2,axiom,(
% 1.39/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.39/0.54  fof(f196,plain,(
% 1.39/0.54    ( ! [X3] : (~r2_xboole_0(X3,sK1)) ) | ~spl5_5),
% 1.39/0.54    inference(resolution,[],[f73,f35])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.39/0.54  fof(f73,plain,(
% 1.39/0.54    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl5_5),
% 1.39/0.54    inference(avatar_component_clause,[],[f72])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f23,f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.39/0.54  fof(f233,plain,(
% 1.39/0.54    spl5_14 | ~spl5_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f217,f72,f229])).
% 1.39/0.54  fof(f217,plain,(
% 1.39/0.54    sK1 = k4_xboole_0(sK1,sK1) | ~spl5_5),
% 1.39/0.54    inference(superposition,[],[f209,f22])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.39/0.54  fof(f193,plain,(
% 1.39/0.54    ~spl5_10 | spl5_13),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f187])).
% 1.39/0.54  fof(f187,plain,(
% 1.39/0.54    $false | (~spl5_10 | spl5_13)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f108,f183,f31])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.54  fof(f183,plain,(
% 1.39/0.54    ~r1_tarski(sK0,sK0) | spl5_13),
% 1.39/0.54    inference(avatar_component_clause,[],[f181])).
% 1.39/0.54  fof(f181,plain,(
% 1.39/0.54    spl5_13 <=> r1_tarski(sK0,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.39/0.54  % (19840)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  fof(f108,plain,(
% 1.39/0.54    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl5_10),
% 1.39/0.54    inference(avatar_component_clause,[],[f107])).
% 1.39/0.54  fof(f107,plain,(
% 1.39/0.54    spl5_10 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.39/0.54  fof(f184,plain,(
% 1.39/0.54    ~spl5_13 | spl5_1 | ~spl5_12),
% 1.39/0.54    inference(avatar_split_clause,[],[f159,f142,f45,f181])).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    spl5_1 <=> k1_xboole_0 = sK0),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.39/0.54  fof(f142,plain,(
% 1.39/0.54    spl5_12 <=> sK0 = k4_xboole_0(sK0,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.39/0.54  fof(f159,plain,(
% 1.39/0.54    k1_xboole_0 = sK0 | ~r1_tarski(sK0,sK0) | ~spl5_12),
% 1.39/0.54    inference(superposition,[],[f144,f33])).
% 1.39/0.54  fof(f144,plain,(
% 1.39/0.54    sK0 = k4_xboole_0(sK0,sK0) | ~spl5_12),
% 1.39/0.54    inference(avatar_component_clause,[],[f142])).
% 1.39/0.54  fof(f154,plain,(
% 1.39/0.54    spl5_9 | ~spl5_11),
% 1.39/0.54    inference(avatar_split_clause,[],[f153,f110,f102])).
% 1.39/0.54  fof(f102,plain,(
% 1.39/0.54    spl5_9 <=> r1_tarski(sK1,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.39/0.54  fof(f110,plain,(
% 1.39/0.54    spl5_11 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.39/0.54  fof(f153,plain,(
% 1.39/0.54    r1_tarski(sK1,sK0) | ~spl5_11),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f150])).
% 1.39/0.54  fof(f150,plain,(
% 1.39/0.54    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl5_11),
% 1.39/0.54    inference(resolution,[],[f147,f31])).
% 1.39/0.54  fof(f147,plain,(
% 1.39/0.54    ( ! [X1] : (~r2_hidden(sK3(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl5_11),
% 1.39/0.54    inference(resolution,[],[f111,f32])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f111,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_11),
% 1.39/0.54    inference(avatar_component_clause,[],[f110])).
% 1.39/0.54  % (19842)Refutation not found, incomplete strategy% (19842)------------------------------
% 1.39/0.54  % (19842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (19842)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (19842)Memory used [KB]: 6140
% 1.39/0.54  % (19842)Time elapsed: 0.114 s
% 1.39/0.54  % (19842)------------------------------
% 1.39/0.54  % (19842)------------------------------
% 1.39/0.54  fof(f145,plain,(
% 1.39/0.54    spl5_12 | ~spl5_10),
% 1.39/0.54    inference(avatar_split_clause,[],[f129,f107,f142])).
% 1.39/0.54  fof(f129,plain,(
% 1.39/0.54    sK0 = k4_xboole_0(sK0,sK0) | ~spl5_10),
% 1.39/0.54    inference(superposition,[],[f124,f124])).
% 1.39/0.54  fof(f124,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ) | ~spl5_10),
% 1.39/0.54    inference(resolution,[],[f116,f40])).
% 1.39/0.54  fof(f116,plain,(
% 1.39/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0) ) | ~spl5_10),
% 1.39/0.54    inference(resolution,[],[f115,f29])).
% 1.39/0.54  fof(f115,plain,(
% 1.39/0.54    ( ! [X3] : (~r2_xboole_0(X3,sK0)) ) | ~spl5_10),
% 1.39/0.54    inference(resolution,[],[f108,f35])).
% 1.39/0.54  fof(f112,plain,(
% 1.39/0.54    spl5_10 | spl5_11 | ~spl5_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f69,f60,f110,f107])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    spl5_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.39/0.54  fof(f69,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl5_4),
% 1.39/0.54    inference(resolution,[],[f65,f39])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.39/0.54  fof(f65,plain,(
% 1.39/0.54    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl5_4),
% 1.39/0.54    inference(superposition,[],[f38,f62])).
% 1.39/0.54  fof(f62,plain,(
% 1.39/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl5_4),
% 1.39/0.54    inference(avatar_component_clause,[],[f60])).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f9])).
% 1.39/0.54  fof(f105,plain,(
% 1.39/0.54    ~spl5_9 | spl5_3 | spl5_8),
% 1.39/0.54    inference(avatar_split_clause,[],[f100,f92,f55,f102])).
% 1.39/0.54  fof(f55,plain,(
% 1.39/0.54    spl5_3 <=> sK0 = sK1),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.39/0.54  fof(f92,plain,(
% 1.39/0.54    spl5_8 <=> r2_xboole_0(sK1,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.39/0.54  fof(f100,plain,(
% 1.39/0.54    sK0 = sK1 | ~r1_tarski(sK1,sK0) | spl5_8),
% 1.39/0.54    inference(resolution,[],[f94,f29])).
% 1.39/0.54  fof(f94,plain,(
% 1.39/0.54    ~r2_xboole_0(sK1,sK0) | spl5_8),
% 1.39/0.54    inference(avatar_component_clause,[],[f92])).
% 1.39/0.54  fof(f95,plain,(
% 1.39/0.54    ~spl5_8 | ~spl5_6),
% 1.39/0.54    inference(avatar_split_clause,[],[f90,f75,f92])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    spl5_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.39/0.54  fof(f90,plain,(
% 1.39/0.54    ~r2_xboole_0(sK1,sK0) | ~spl5_6),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f88])).
% 1.39/0.54  fof(f88,plain,(
% 1.39/0.54    ~r2_xboole_0(sK1,sK0) | ~r2_xboole_0(sK1,sK0) | ~spl5_6),
% 1.39/0.54    inference(resolution,[],[f79,f35])).
% 1.39/0.54  fof(f79,plain,(
% 1.39/0.54    ( ! [X1] : (~r2_hidden(sK4(sK1,X1),sK0) | ~r2_xboole_0(sK1,X1)) ) | ~spl5_6),
% 1.39/0.54    inference(resolution,[],[f76,f36])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f76,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl5_6),
% 1.39/0.54    inference(avatar_component_clause,[],[f75])).
% 1.39/0.54  fof(f77,plain,(
% 1.39/0.54    spl5_5 | spl5_6 | ~spl5_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f67,f60,f75,f72])).
% 1.39/0.54  fof(f67,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl5_4),
% 1.39/0.54    inference(resolution,[],[f64,f39])).
% 1.39/0.54  % (19841)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.54  fof(f64,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl5_4),
% 1.39/0.54    inference(superposition,[],[f37,f62])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f9])).
% 1.39/0.54  fof(f63,plain,(
% 1.39/0.54    spl5_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f18,f60])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,plain,(
% 1.39/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.39/0.54    inference(flattening,[],[f13])).
% 1.39/0.54  fof(f13,plain,(
% 1.39/0.54    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.54    inference(negated_conjecture,[],[f10])).
% 1.39/0.54  fof(f10,conjecture,(
% 1.39/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.39/0.54  fof(f58,plain,(
% 1.39/0.54    ~spl5_3),
% 1.39/0.54    inference(avatar_split_clause,[],[f21,f55])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    sK0 != sK1),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    ~spl5_2),
% 1.39/0.54    inference(avatar_split_clause,[],[f20,f50])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    k1_xboole_0 != sK1),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    ~spl5_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f19,f45])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    k1_xboole_0 != sK0),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (19860)------------------------------
% 1.39/0.54  % (19860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (19860)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (19860)Memory used [KB]: 10746
% 1.39/0.54  % (19860)Time elapsed: 0.121 s
% 1.39/0.54  % (19860)------------------------------
% 1.39/0.54  % (19860)------------------------------
% 1.39/0.54  % (19837)Success in time 0.177 s
%------------------------------------------------------------------------------
