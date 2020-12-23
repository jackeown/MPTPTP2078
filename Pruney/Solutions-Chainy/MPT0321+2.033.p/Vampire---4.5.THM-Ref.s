%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
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
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f70,f75,f110,f118,f127,f143,f158,f163,f208,f221,f233,f247])).

fof(f247,plain,
    ( spl10_4
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl10_4
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f69,f108,f99,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f99,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl10_7
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f108,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_9
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f69,plain,
    ( sK0 != sK2
    | spl10_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl10_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f233,plain,
    ( spl10_6
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f232,f206,f94])).

fof(f94,plain,
    ( spl10_6
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f206,plain,
    ( spl10_18
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f232,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl10_18 ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl10_18 ),
    inference(resolution,[],[f223,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f223,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(X1,sK3),sK1)
        | r1_tarski(X1,sK3) )
    | ~ spl10_18 ),
    inference(resolution,[],[f207,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f207,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f221,plain,
    ( spl10_1
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl10_1
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f55,f23,f213,f26])).

fof(f213,plain,
    ( ! [X2] : r1_tarski(sK0,X2)
    | ~ spl10_13 ),
    inference(resolution,[],[f153,f28])).

fof(f153,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl10_13
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f208,plain,
    ( spl10_13
    | spl10_18
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f137,f72,f206,f152])).

fof(f72,plain,
    ( spl10_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f85,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X11,sK3) )
    | ~ spl10_5 ),
    inference(superposition,[],[f43,f74])).

fof(f74,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f163,plain,
    ( spl10_3
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl10_3
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f65,f96,f105,f26])).

% (24216)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f105,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_8
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f96,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f65,plain,
    ( sK1 != sK3
    | spl10_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f158,plain,
    ( spl10_9
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f157,f125,f107])).

fof(f125,plain,
    ( spl10_11
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f157,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl10_11 ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl10_11 ),
    inference(resolution,[],[f145,f28])).

fof(f145,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(X1,sK2),sK0)
        | r1_tarski(X1,sK2) )
    | ~ spl10_11 ),
    inference(resolution,[],[f126,f29])).

fof(f126,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f143,plain,
    ( spl10_2
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl10_2
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f60,f23,f130,f26])).

fof(f130,plain,
    ( ! [X2] : r1_tarski(sK1,X2)
    | ~ spl10_10 ),
    inference(resolution,[],[f123,f28])).

fof(f123,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl10_10
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f127,plain,
    ( spl10_10
    | spl10_11
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f119,f72,f125,f122])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f84,f44])).

fof(f84,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X8,sK2) )
    | ~ spl10_5 ),
    inference(superposition,[],[f42,f74])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f118,plain,
    ( spl10_7
    | spl10_2
    | ~ spl10_6
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f115,f72,f94,f58,f98])).

fof(f115,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1
    | r1_tarski(sK2,sK0)
    | ~ spl10_5 ),
    inference(resolution,[],[f79,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f79,plain,
    ( ! [X3] :
        ( r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X3,sK3) )
    | ~ spl10_5 ),
    inference(superposition,[],[f39,f74])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f110,plain,
    ( spl10_8
    | spl10_1
    | ~ spl10_9
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f90,f72,f107,f53,f103])).

fof(f90,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0
    | r1_tarski(sK3,sK1)
    | ~ spl10_5 ),
    inference(resolution,[],[f77,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,
    ( ! [X1] :
        ( r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X1,sK2) )
    | ~ spl10_5 ),
    inference(superposition,[],[f38,f74])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f19,f72])).

fof(f19,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f70,plain,
    ( ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f18,f67,f63])).

fof(f18,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f21,f58])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (24205)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (24221)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (24201)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (24199)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (24200)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (24213)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (24221)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (24227)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (24222)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (24211)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24214)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (24204)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f56,f61,f70,f75,f110,f118,f127,f143,f158,f163,f208,f221,f233,f247])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    spl10_4 | ~spl10_7 | ~spl10_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    $false | (spl10_4 | ~spl10_7 | ~spl10_9)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f69,f108,f99,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0) | ~spl10_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    spl10_7 <=> r1_tarski(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    r1_tarski(sK0,sK2) | ~spl10_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl10_9 <=> r1_tarski(sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    sK0 != sK2 | spl10_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl10_4 <=> sK0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    spl10_6 | ~spl10_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f232,f206,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl10_6 <=> r1_tarski(sK1,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    spl10_18 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    r1_tarski(sK1,sK3) | ~spl10_18),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f230])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl10_18),
% 0.21/0.53    inference(resolution,[],[f223,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK4(X1,sK3),sK1) | r1_tarski(X1,sK3)) ) | ~spl10_18),
% 0.21/0.53    inference(resolution,[],[f207,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl10_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f206])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    spl10_1 | ~spl10_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f218])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    $false | (spl10_1 | ~spl10_13)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f55,f23,f213,f26])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(sK0,X2)) ) | ~spl10_13),
% 0.21/0.53    inference(resolution,[],[f153,f28])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl10_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl10_13 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | spl10_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl10_1 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl10_13 | spl10_18 | ~spl10_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f137,f72,f206,f152])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl10_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl10_5),
% 0.21/0.53    inference(resolution,[],[f85,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X10,X11] : (~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X11,sK3)) ) | ~spl10_5),
% 0.21/0.53    inference(superposition,[],[f43,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl10_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f72])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    spl10_3 | ~spl10_6 | ~spl10_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    $false | (spl10_3 | ~spl10_6 | ~spl10_8)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f65,f96,f105,f26])).
% 0.21/0.53  % (24216)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    r1_tarski(sK3,sK1) | ~spl10_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl10_8 <=> r1_tarski(sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    r1_tarski(sK1,sK3) | ~spl10_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f94])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    sK1 != sK3 | spl10_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl10_3 <=> sK1 = sK3),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    spl10_9 | ~spl10_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f157,f125,f107])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl10_11 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    r1_tarski(sK0,sK2) | ~spl10_11),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f155])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl10_11),
% 0.21/0.53    inference(resolution,[],[f145,f28])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK4(X1,sK2),sK0) | r1_tarski(X1,sK2)) ) | ~spl10_11),
% 0.21/0.53    inference(resolution,[],[f126,f29])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl10_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    spl10_2 | ~spl10_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    $false | (spl10_2 | ~spl10_10)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f60,f23,f130,f26])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(sK1,X2)) ) | ~spl10_10),
% 0.21/0.53    inference(resolution,[],[f123,f28])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl10_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    spl10_10 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl10_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl10_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl10_10 | spl10_11 | ~spl10_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f119,f72,f125,f122])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl10_5),
% 0.21/0.53    inference(resolution,[],[f84,f44])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X8,sK2)) ) | ~spl10_5),
% 0.21/0.53    inference(superposition,[],[f42,f74])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl10_7 | spl10_2 | ~spl10_6 | ~spl10_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f115,f72,f94,f58,f98])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1 | r1_tarski(sK2,sK0) | ~spl10_5),
% 0.21/0.53    inference(resolution,[],[f79,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X3,sK3)) ) | ~spl10_5),
% 0.21/0.53    inference(superposition,[],[f39,f74])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl10_8 | spl10_1 | ~spl10_9 | ~spl10_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f90,f72,f107,f53,f103])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0 | r1_tarski(sK3,sK1) | ~spl10_5),
% 0.21/0.53    inference(resolution,[],[f77,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X1,sK2)) ) | ~spl10_5),
% 0.21/0.53    inference(superposition,[],[f38,f74])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl10_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f19,f72])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ~spl10_3 | ~spl10_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f18,f67,f63])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    sK0 != sK2 | sK1 != sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ~spl10_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f21,f58])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~spl10_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f20,f53])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (24221)------------------------------
% 0.21/0.53  % (24221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24221)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (24221)Memory used [KB]: 10874
% 0.21/0.53  % (24221)Time elapsed: 0.113 s
% 0.21/0.53  % (24221)------------------------------
% 0.21/0.53  % (24221)------------------------------
% 0.21/0.53  % (24202)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (24198)Success in time 0.174 s
%------------------------------------------------------------------------------
