%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 141 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  238 ( 431 expanded)
%              Number of equality atoms :   32 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f53,f58,f63,f67,f71,f75,f79,f91,f97,f102,f108,f126,f133,f139,f161])).

fof(f161,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl3_4
    | spl3_5
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f57,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f159,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f158,f52])).

fof(f52,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f158,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f144,f107])).

fof(f107,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_16
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f144,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_9
    | ~ spl3_21 ),
    inference(superposition,[],[f74,f138])).

fof(f138,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_21
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f139,plain,
    ( spl3_21
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f134,f130,f69,f136])).

fof(f69,plain,
    ( spl3_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f130,plain,
    ( spl3_20
  <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f134,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(resolution,[],[f132,f70])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f132,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl3_20
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f127,f124,f94,f130])).

fof(f94,plain,
    ( spl3_14
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f124,plain,
    ( spl3_19
  <=> ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
        | ~ m1_setfam_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f127,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(resolution,[],[f125,f96])).

fof(f96,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_setfam_1(k1_xboole_0,X0)
        | r1_tarski(X0,k1_xboole_0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f124])).

fof(f126,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f122,f89,f60,f124])).

fof(f60,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f89,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f122,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
        | ~ m1_setfam_1(k1_xboole_0,X0) )
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(superposition,[],[f90,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f108,plain,
    ( spl3_16
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f103,f100,f77,f105])).

fof(f77,plain,
    ( spl3_10
  <=> ! [X0] : v1_xboole_0(sK2(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f100,plain,
    ( spl3_15
  <=> ! [X0] : k1_xboole_0 = sK2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f103,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(superposition,[],[f78,f101])).

fof(f101,plain,
    ( ! [X0] : k1_xboole_0 = sK2(X0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f78,plain,
    ( ! [X0] : v1_xboole_0(sK2(X0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f102,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f98,f77,f65,f100])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f98,plain,
    ( ! [X0] : k1_xboole_0 = sK2(X0)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f66,f78])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f97,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f92,f40,f35,f94])).

fof(f35,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,
    ( spl3_2
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f42,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f91,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f32,f89])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f79,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    ! [X0] : v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f71,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f67,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f63,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f58,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f35])).

fof(f25,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:08:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (1906)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (1906)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f162,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f38,f43,f53,f58,f63,f67,f71,f75,f79,f91,f97,f102,f108,f126,f133,f139,f161])).
% 0.22/0.42  fof(f161,plain,(
% 0.22/0.42    ~spl3_4 | spl3_5 | ~spl3_9 | ~spl3_16 | ~spl3_21),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f160])).
% 0.22/0.42  fof(f160,plain,(
% 0.22/0.42    $false | (~spl3_4 | spl3_5 | ~spl3_9 | ~spl3_16 | ~spl3_21)),
% 0.22/0.42    inference(subsumption_resolution,[],[f159,f57])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ~v2_struct_0(sK0) | spl3_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f55])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl3_5 <=> v2_struct_0(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.42  fof(f159,plain,(
% 0.22/0.42    v2_struct_0(sK0) | (~spl3_4 | ~spl3_9 | ~spl3_16 | ~spl3_21)),
% 0.22/0.42    inference(subsumption_resolution,[],[f158,f52])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    l1_struct_0(sK0) | ~spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f50])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl3_4 <=> l1_struct_0(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f158,plain,(
% 0.22/0.42    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_9 | ~spl3_16 | ~spl3_21)),
% 0.22/0.42    inference(subsumption_resolution,[],[f144,f107])).
% 0.22/0.42  fof(f107,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0) | ~spl3_16),
% 0.22/0.42    inference(avatar_component_clause,[],[f105])).
% 0.22/0.42  fof(f105,plain,(
% 0.22/0.42    spl3_16 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.42  fof(f144,plain,(
% 0.22/0.42    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_9 | ~spl3_21)),
% 0.22/0.42    inference(superposition,[],[f74,f138])).
% 0.22/0.42  fof(f138,plain,(
% 0.22/0.42    k1_xboole_0 = u1_struct_0(sK0) | ~spl3_21),
% 0.22/0.42    inference(avatar_component_clause,[],[f136])).
% 0.22/0.42  fof(f136,plain,(
% 0.22/0.42    spl3_21 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f73])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    spl3_9 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.42  fof(f139,plain,(
% 0.22/0.42    spl3_21 | ~spl3_8 | ~spl3_20),
% 0.22/0.42    inference(avatar_split_clause,[],[f134,f130,f69,f136])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl3_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.42  fof(f130,plain,(
% 0.22/0.42    spl3_20 <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.42  fof(f134,plain,(
% 0.22/0.42    k1_xboole_0 = u1_struct_0(sK0) | (~spl3_8 | ~spl3_20)),
% 0.22/0.42    inference(resolution,[],[f132,f70])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f69])).
% 0.22/0.42  fof(f132,plain,(
% 0.22/0.42    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | ~spl3_20),
% 0.22/0.42    inference(avatar_component_clause,[],[f130])).
% 0.22/0.42  fof(f133,plain,(
% 0.22/0.42    spl3_20 | ~spl3_14 | ~spl3_19),
% 0.22/0.42    inference(avatar_split_clause,[],[f127,f124,f94,f130])).
% 0.22/0.42  fof(f94,plain,(
% 0.22/0.42    spl3_14 <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.42  fof(f124,plain,(
% 0.22/0.42    spl3_19 <=> ! [X0] : (r1_tarski(X0,k1_xboole_0) | ~m1_setfam_1(k1_xboole_0,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.42  fof(f127,plain,(
% 0.22/0.42    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | (~spl3_14 | ~spl3_19)),
% 0.22/0.42    inference(resolution,[],[f125,f96])).
% 0.22/0.42  fof(f96,plain,(
% 0.22/0.42    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl3_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f94])).
% 0.22/0.42  fof(f125,plain,(
% 0.22/0.42    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | r1_tarski(X0,k1_xboole_0)) ) | ~spl3_19),
% 0.22/0.42    inference(avatar_component_clause,[],[f124])).
% 0.22/0.42  fof(f126,plain,(
% 0.22/0.42    spl3_19 | ~spl3_6 | ~spl3_13),
% 0.22/0.42    inference(avatar_split_clause,[],[f122,f89,f60,f124])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    spl3_6 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.42  fof(f89,plain,(
% 0.22/0.42    spl3_13 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.42  fof(f122,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | ~m1_setfam_1(k1_xboole_0,X0)) ) | (~spl3_6 | ~spl3_13)),
% 0.22/0.42    inference(superposition,[],[f90,f62])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl3_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f60])).
% 0.22/0.42  fof(f90,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) ) | ~spl3_13),
% 0.22/0.42    inference(avatar_component_clause,[],[f89])).
% 0.22/0.42  fof(f108,plain,(
% 0.22/0.42    spl3_16 | ~spl3_10 | ~spl3_15),
% 0.22/0.42    inference(avatar_split_clause,[],[f103,f100,f77,f105])).
% 0.22/0.42  fof(f77,plain,(
% 0.22/0.42    spl3_10 <=> ! [X0] : v1_xboole_0(sK2(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.42  fof(f100,plain,(
% 0.22/0.42    spl3_15 <=> ! [X0] : k1_xboole_0 = sK2(X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0) | (~spl3_10 | ~spl3_15)),
% 0.22/0.42    inference(superposition,[],[f78,f101])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = sK2(X0)) ) | ~spl3_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f100])).
% 0.22/0.42  fof(f78,plain,(
% 0.22/0.42    ( ! [X0] : (v1_xboole_0(sK2(X0))) ) | ~spl3_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f77])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    spl3_15 | ~spl3_7 | ~spl3_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f98,f77,f65,f100])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    spl3_7 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.42  fof(f98,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = sK2(X0)) ) | (~spl3_7 | ~spl3_10)),
% 0.22/0.42    inference(resolution,[],[f66,f78])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f65])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    spl3_14 | ~spl3_1 | ~spl3_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f92,f40,f35,f94])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl3_1 <=> k1_xboole_0 = sK1),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl3_2 <=> m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.42  fof(f92,plain,(
% 0.22/0.42    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.42    inference(superposition,[],[f42,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    k1_xboole_0 = sK1 | ~spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    m1_setfam_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f40])).
% 0.22/0.42  fof(f91,plain,(
% 0.22/0.42    spl3_13),
% 0.22/0.42    inference(avatar_split_clause,[],[f32,f89])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.22/0.42    inference(nnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.22/0.42  fof(f79,plain,(
% 0.22/0.42    spl3_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f31,f77])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    ( ! [X0] : (v1_xboole_0(sK2(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    spl3_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f29,f73])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.42    inference(flattening,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    spl3_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f28,f69])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl3_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f27,f65])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    spl3_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f26,f60])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ~spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f21,f55])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ~v2_struct_0(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.42    inference(flattening,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,negated_conjecture,(
% 0.22/0.42    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.22/0.42    inference(negated_conjecture,[],[f7])).
% 0.22/0.42  fof(f7,conjecture,(
% 0.22/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl3_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f22,f50])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    l1_struct_0(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    spl3_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f40])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    spl3_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f25,f35])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    k1_xboole_0 = sK1),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (1906)------------------------------
% 0.22/0.42  % (1906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (1906)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (1906)Memory used [KB]: 10618
% 0.22/0.42  % (1906)Time elapsed: 0.008 s
% 0.22/0.42  % (1906)------------------------------
% 0.22/0.42  % (1906)------------------------------
% 0.22/0.43  % (1899)Success in time 0.065 s
%------------------------------------------------------------------------------
