%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 160 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :    7
%              Number of atoms          :  229 ( 435 expanded)
%              Number of equality atoms :   43 ( 128 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f129,f134,f169,f177,f186,f206,f212,f217,f277,f291,f300,f316])).

fof(f316,plain,
    ( spl8_4
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl8_4
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f128,f167,f158,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f158,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl8_7
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f167,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_9
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f128,plain,
    ( sK0 != sK2
    | spl8_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f300,plain,
    ( spl8_6
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f299,f275,f153])).

fof(f153,plain,
    ( spl8_6
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f275,plain,
    ( spl8_18
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f299,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl8_18 ),
    inference(resolution,[],[f295,f64])).

% (32341)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f295,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK3),sK1)
        | r1_tarski(X0,sK3) )
    | ~ spl8_18 ),
    inference(resolution,[],[f276,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f276,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f275])).

fof(f291,plain,
    ( spl8_1
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl8_1
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f114,f44,f281,f59])).

fof(f281,plain,
    ( ! [X4] : r1_tarski(sK0,X4)
    | ~ spl8_17 ),
    inference(resolution,[],[f273,f64])).

fof(f273,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl8_17
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f114,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f277,plain,
    ( spl8_17
    | spl8_18
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f196,f131,f275,f272])).

fof(f131,plain,
    ( spl8_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f144,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

% (32353)Refutation not found, incomplete strategy% (32353)------------------------------
% (32353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32353)Termination reason: Refutation not found, incomplete strategy

% (32353)Memory used [KB]: 10618
% (32353)Time elapsed: 0.118 s
% (32353)------------------------------
% (32353)------------------------------
fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f144,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X11,sK3) )
    | ~ spl8_5 ),
    inference(superposition,[],[f82,f133])).

fof(f133,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f217,plain,
    ( spl8_3
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl8_3
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f124,f155,f164,f59])).

fof(f164,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_8
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f155,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f124,plain,
    ( sK1 != sK3
    | spl8_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f212,plain,
    ( spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f211,f184,f166])).

fof(f184,plain,
    ( spl8_11
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f211,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl8_11 ),
    inference(resolution,[],[f207,f64])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK2),sK0)
        | r1_tarski(X0,sK2) )
    | ~ spl8_11 ),
    inference(resolution,[],[f185,f65])).

fof(f185,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f206,plain,
    ( spl8_2
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl8_2
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f119,f44,f191,f59])).

fof(f191,plain,
    ( ! [X4] : r1_tarski(sK1,X4)
    | ~ spl8_10 ),
    inference(resolution,[],[f182,f64])).

fof(f182,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl8_10
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f119,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f186,plain,
    ( spl8_10
    | spl8_11
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f178,f131,f184,f181])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f143,f83])).

fof(f143,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X8,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f81,f133])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f177,plain,
    ( spl8_7
    | spl8_2
    | ~ spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f174,f131,f153,f117,f157])).

fof(f174,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1
    | r1_tarski(sK2,sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f138,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f138,plain,
    ( ! [X3] :
        ( r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X3,sK3) )
    | ~ spl8_5 ),
    inference(superposition,[],[f71,f133])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f169,plain,
    ( spl8_8
    | spl8_1
    | ~ spl8_9
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f149,f131,f166,f112,f162])).

fof(f149,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0
    | r1_tarski(sK3,sK1)
    | ~ spl8_5 ),
    inference(resolution,[],[f136,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,
    ( ! [X1] :
        ( r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X1,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f70,f133])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f134,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f40,f131])).

fof(f40,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f129,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f39,f126,f122])).

fof(f39,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f120,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f42,f117])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f115,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f41,f112])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (32338)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (32358)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (32342)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (32361)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (32347)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (32363)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (32353)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (32358)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f115,f120,f129,f134,f169,f177,f186,f206,f212,f217,f277,f291,f300,f316])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    spl8_4 | ~spl8_7 | ~spl8_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f312])).
% 0.21/0.53  fof(f312,plain,(
% 0.21/0.53    $false | (spl8_4 | ~spl8_7 | ~spl8_9)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f128,f167,f158,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0) | ~spl8_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f157])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    spl8_7 <=> r1_tarski(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    r1_tarski(sK0,sK2) | ~spl8_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f166])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl8_9 <=> r1_tarski(sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    sK0 != sK2 | spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl8_4 <=> sK0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    spl8_6 | ~spl8_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f299,f275,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    spl8_6 <=> r1_tarski(sK1,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    spl8_18 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    r1_tarski(sK1,sK3) | ~spl8_18),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f297])).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl8_18),
% 0.21/0.53    inference(resolution,[],[f295,f64])).
% 0.21/0.54  % (32341)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f295,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5(X0,sK3),sK1) | r1_tarski(X0,sK3)) ) | ~spl8_18),
% 0.21/0.54    inference(resolution,[],[f276,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl8_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f275])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    spl8_1 | ~spl8_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    $false | (spl8_1 | ~spl8_17)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f114,f44,f281,f59])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    ( ! [X4] : (r1_tarski(sK0,X4)) ) | ~spl8_17),
% 0.21/0.54    inference(resolution,[],[f273,f64])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl8_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f272])).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    spl8_17 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | spl8_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f112])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    spl8_1 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    spl8_17 | spl8_18 | ~spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f196,f131,f275,f272])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl8_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl8_5),
% 0.21/0.54    inference(resolution,[],[f144,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % (32353)Refutation not found, incomplete strategy% (32353)------------------------------
% 0.21/0.54  % (32353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32353)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32353)Memory used [KB]: 10618
% 0.21/0.54  % (32353)Time elapsed: 0.118 s
% 0.21/0.54  % (32353)------------------------------
% 0.21/0.54  % (32353)------------------------------
% 0.21/0.54  fof(f24,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X10,X11] : (~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X11,sK3)) ) | ~spl8_5),
% 0.21/0.54    inference(superposition,[],[f82,f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl8_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f131])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    spl8_3 | ~spl8_6 | ~spl8_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f214])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    $false | (spl8_3 | ~spl8_6 | ~spl8_8)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f124,f155,f164,f59])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    r1_tarski(sK3,sK1) | ~spl8_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f162])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl8_8 <=> r1_tarski(sK3,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    r1_tarski(sK1,sK3) | ~spl8_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f153])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    sK1 != sK3 | spl8_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f122])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    spl8_3 <=> sK1 = sK3),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    spl8_9 | ~spl8_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f211,f184,f166])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    spl8_11 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    r1_tarski(sK0,sK2) | ~spl8_11),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f209])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl8_11),
% 0.21/0.54    inference(resolution,[],[f207,f64])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5(X0,sK2),sK0) | r1_tarski(X0,sK2)) ) | ~spl8_11),
% 0.21/0.54    inference(resolution,[],[f185,f65])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl8_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f184])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    spl8_2 | ~spl8_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    $false | (spl8_2 | ~spl8_10)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f119,f44,f191,f59])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    ( ! [X4] : (r1_tarski(sK1,X4)) ) | ~spl8_10),
% 0.21/0.54    inference(resolution,[],[f182,f64])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f181])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    spl8_10 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | spl8_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    spl8_10 | spl8_11 | ~spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f178,f131,f184,f181])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_5),
% 0.21/0.54    inference(resolution,[],[f143,f83])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X8,sK2)) ) | ~spl8_5),
% 0.21/0.54    inference(superposition,[],[f81,f133])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    spl8_7 | spl8_2 | ~spl8_6 | ~spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f174,f131,f153,f117,f157])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1 | r1_tarski(sK2,sK0) | ~spl8_5),
% 0.21/0.54    inference(resolution,[],[f138,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X3,sK3)) ) | ~spl8_5),
% 0.21/0.54    inference(superposition,[],[f71,f133])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    spl8_8 | spl8_1 | ~spl8_9 | ~spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f149,f131,f166,f112,f162])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0 | r1_tarski(sK3,sK1) | ~spl8_5),
% 0.21/0.54    inference(resolution,[],[f136,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X1,sK2)) ) | ~spl8_5),
% 0.21/0.54    inference(superposition,[],[f70,f133])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f131])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f27])).
% 0.21/0.54  fof(f27,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ~spl8_3 | ~spl8_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f126,f122])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    sK0 != sK2 | sK1 != sK3),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ~spl8_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f117])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ~spl8_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f112])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    k1_xboole_0 != sK0),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (32358)------------------------------
% 0.21/0.54  % (32358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32358)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (32358)Memory used [KB]: 10874
% 0.21/0.54  % (32358)Time elapsed: 0.025 s
% 0.21/0.54  % (32358)------------------------------
% 0.21/0.54  % (32358)------------------------------
% 0.21/0.54  % (32335)Success in time 0.183 s
%------------------------------------------------------------------------------
