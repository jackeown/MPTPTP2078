%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f56,f61,f96,f104,f113,f127,f133,f138,f186,f194,f203,f216])).

fof(f216,plain,
    ( spl6_4
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f55,f94,f85,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f85,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_7
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f94,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_9
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f55,plain,
    ( sK0 != sK2
    | spl6_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f203,plain,
    ( spl6_6
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f202,f184,f80])).

fof(f80,plain,
    ( spl6_6
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f184,plain,
    ( spl6_17
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f202,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_17 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl6_17 ),
    inference(resolution,[],[f199,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f199,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK3),sK1)
        | r1_tarski(X1,sK3) )
    | ~ spl6_17 ),
    inference(resolution,[],[f185,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f185,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f194,plain,
    ( spl6_1
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl6_1
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f41,f20,f189,f25])).

fof(f189,plain,
    ( ! [X3] : r1_tarski(sK0,X3)
    | ~ spl6_16 ),
    inference(resolution,[],[f182,f27])).

fof(f182,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_16
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f20,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f186,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f121,f58,f184,f181])).

fof(f58,plain,
    ( spl6_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f71,f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f71,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X11,sK3) )
    | ~ spl6_5 ),
    inference(superposition,[],[f34,f60])).

fof(f60,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f138,plain,
    ( spl6_3
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f51,f82,f91,f25])).

fof(f91,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_8
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f82,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f51,plain,
    ( sK1 != sK3
    | spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f133,plain,
    ( spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f132,f111,f93])).

fof(f111,plain,
    ( spl6_11
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f132,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_11 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f129,f27])).

fof(f129,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK2),sK0)
        | r1_tarski(X1,sK2) )
    | ~ spl6_11 ),
    inference(resolution,[],[f112,f28])).

fof(f112,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f127,plain,
    ( spl6_2
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f46,f20,f117,f25])).

fof(f117,plain,
    ( ! [X3] : r1_tarski(sK1,X3)
    | ~ spl6_10 ),
    inference(resolution,[],[f109,f27])).

fof(f109,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_10
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f113,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f105,f58,f111,f108])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f35])).

fof(f70,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X8,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f33,f60])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f104,plain,
    ( spl6_7
    | spl6_2
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f101,f58,f80,f44,f84])).

fof(f101,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1
    | r1_tarski(sK2,sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f65,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f65,plain,
    ( ! [X3] :
        ( r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X3,sK3) )
    | ~ spl6_5 ),
    inference(superposition,[],[f30,f60])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f96,plain,
    ( spl6_8
    | spl6_1
    | ~ spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f76,f58,f93,f39,f89])).

fof(f76,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0
    | r1_tarski(sK3,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f63,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,
    ( ! [X1] :
        ( r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X1,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f29,f60])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f17,f58])).

fof(f17,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f56,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f16,f53,f49])).

fof(f16,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:57:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (17707)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (17699)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (17711)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (17715)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f42,f47,f56,f61,f96,f104,f113,f127,f133,f138,f186,f194,f203,f216])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    spl6_4 | ~spl6_7 | ~spl6_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f213])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    $false | (spl6_4 | ~spl6_7 | ~spl6_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f55,f94,f85,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    r1_tarski(sK2,sK0) | ~spl6_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl6_7 <=> r1_tarski(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    r1_tarski(sK0,sK2) | ~spl6_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl6_9 <=> r1_tarski(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    sK0 != sK2 | spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl6_4 <=> sK0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    spl6_6 | ~spl6_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f202,f184,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    spl6_6 <=> r1_tarski(sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    spl6_17 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    r1_tarski(sK1,sK3) | ~spl6_17),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f200])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl6_17),
% 0.22/0.51    inference(resolution,[],[f199,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(sK5(X1,sK3),sK1) | r1_tarski(X1,sK3)) ) | ~spl6_17),
% 0.22/0.51    inference(resolution,[],[f185,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl6_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f184])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    spl6_1 | ~spl6_16),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    $false | (spl6_1 | ~spl6_16)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f41,f20,f189,f25])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ( ! [X3] : (r1_tarski(sK0,X3)) ) | ~spl6_16),
% 0.22/0.51    inference(resolution,[],[f182,f27])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f181])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    spl6_16 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    spl6_1 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    spl6_16 | spl6_17 | ~spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f121,f58,f184,f181])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl6_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f71,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X10,X11] : (~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X11,sK3)) ) | ~spl6_5),
% 0.22/0.51    inference(superposition,[],[f34,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl6_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f58])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    spl6_3 | ~spl6_6 | ~spl6_8),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f135])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    $false | (spl6_3 | ~spl6_6 | ~spl6_8)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f51,f82,f91,f25])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    r1_tarski(sK3,sK1) | ~spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl6_8 <=> r1_tarski(sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    r1_tarski(sK1,sK3) | ~spl6_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f80])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    sK1 != sK3 | spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl6_3 <=> sK1 = sK3),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    spl6_9 | ~spl6_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f132,f111,f93])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl6_11 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    r1_tarski(sK0,sK2) | ~spl6_11),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f130])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl6_11),
% 0.22/0.51    inference(resolution,[],[f129,f27])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(sK5(X1,sK2),sK0) | r1_tarski(X1,sK2)) ) | ~spl6_11),
% 0.22/0.51    inference(resolution,[],[f112,f28])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl6_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f111])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl6_2 | ~spl6_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f124])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    $false | (spl6_2 | ~spl6_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f46,f20,f117,f25])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ( ! [X3] : (r1_tarski(sK1,X3)) ) | ~spl6_10),
% 0.22/0.51    inference(resolution,[],[f109,f27])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl6_10 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl6_2 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl6_10 | spl6_11 | ~spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f105,f58,f111,f108])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f70,f35])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X8,sK2)) ) | ~spl6_5),
% 0.22/0.51    inference(superposition,[],[f33,f60])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl6_7 | spl6_2 | ~spl6_6 | ~spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f101,f58,f80,f44,f84])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1 | r1_tarski(sK2,sK0) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f65,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X3,sK3)) ) | ~spl6_5),
% 0.22/0.51    inference(superposition,[],[f30,f60])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl6_8 | spl6_1 | ~spl6_9 | ~spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f76,f58,f93,f39,f89])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0 | r1_tarski(sK3,sK1) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f63,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X1,sK2)) ) | ~spl6_5),
% 0.22/0.51    inference(superposition,[],[f29,f60])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f58])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~spl6_3 | ~spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f16,f53,f49])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    sK0 != sK2 | sK1 != sK3),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ~spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f18,f39])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (17715)------------------------------
% 0.22/0.52  % (17715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17715)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (17715)Memory used [KB]: 10746
% 0.22/0.52  % (17715)Time elapsed: 0.069 s
% 0.22/0.52  % (17715)------------------------------
% 0.22/0.52  % (17715)------------------------------
% 0.22/0.52  % (17712)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (17701)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (17692)Success in time 0.157 s
%------------------------------------------------------------------------------
