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
% DateTime   : Thu Dec  3 12:58:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 (  98 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 ( 298 expanded)
%              Number of equality atoms :   63 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f50,f68,f72,f76,f83,f88,f101,f109])).

fof(f109,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f107,f29])).

fof(f29,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f107,plain,
    ( k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f105,f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(superposition,[],[f71,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_16
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f101,plain,
    ( spl3_16
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f91,f86,f44,f40,f36,f99])).

fof(f36,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( spl3_4
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(X0,X1)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f91,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f41,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f90,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f45,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f89,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(resolution,[],[f87,f37])).

fof(f37,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | ~ v1_relat_1(X1)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | k1_xboole_0 = X1 )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f84,f81,f48,f86])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(X0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
        | ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,
    ( spl3_13
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f79,f74,f66,f81])).

fof(f66,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f74,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,X1)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(resolution,[],[f75,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X1)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f20,f74])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f72,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f68,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f21,f66])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f42,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f36])).

fof(f14,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (3260)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (3253)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (3253)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f50,f68,f72,f76,f83,f88,f101,f109])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl3_1 | spl3_2 | ~spl3_11 | ~spl3_16),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    $false | (spl3_1 | spl3_2 | ~spl3_11 | ~spl3_16)),
% 0.21/0.46    inference(subsumption_resolution,[],[f107,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    k1_xboole_0 != sK0 | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    spl3_1 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | (spl3_2 | ~spl3_11 | ~spl3_16)),
% 0.21/0.46    inference(subsumption_resolution,[],[f105,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl3_11 | ~spl3_16)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl3_11 | ~spl3_16)),
% 0.21/0.46    inference(superposition,[],[f71,f100])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f99])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl3_16 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl3_11 <=> ! [X1,X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl3_16 | ~spl3_3 | spl3_4 | ~spl3_5 | ~spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f91,f86,f44,f40,f36,f99])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl3_4 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl3_5 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl3_14 <=> ! [X1,X0] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1) | ~m1_subset_1(X0,X1) | k1_xboole_0 = X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | spl3_4 | ~spl3_5 | ~spl3_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f90,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f40])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | ~spl3_5 | ~spl3_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f89,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_3 | ~spl3_14)),
% 0.21/0.46    inference(resolution,[],[f87,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f36])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | k1_xboole_0 = X1) ) | ~spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f86])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl3_14 | ~spl3_6 | ~spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f84,f81,f48,f86])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl3_6 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_13 <=> ! [X1,X0] : (~v1_relat_1(X0) | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 | v1_xboole_0(X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1) | ~m1_subset_1(X0,X1) | k1_xboole_0 = X1) ) | (~spl3_6 | ~spl3_13)),
% 0.21/0.46    inference(resolution,[],[f82,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_xboole_0(X0) | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 | ~v1_relat_1(X0) | ~m1_subset_1(X1,X0)) ) | ~spl3_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_13 | ~spl3_10 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f79,f74,f66,f81])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl3_10 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl3_12 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) ) | (~spl3_10 | ~spl3_12)),
% 0.21/0.46    inference(resolution,[],[f75,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f66])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) ) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f74])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f74])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f70])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f66])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f48])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ~spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f40])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f14,f36])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f32])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    k1_xboole_0 != sK1),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f28])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    k1_xboole_0 != sK0),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (3253)------------------------------
% 0.21/0.46  % (3253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3253)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (3253)Memory used [KB]: 10618
% 0.21/0.46  % (3253)Time elapsed: 0.058 s
% 0.21/0.46  % (3253)------------------------------
% 0.21/0.46  % (3253)------------------------------
% 0.21/0.46  % (3243)Success in time 0.111 s
%------------------------------------------------------------------------------
