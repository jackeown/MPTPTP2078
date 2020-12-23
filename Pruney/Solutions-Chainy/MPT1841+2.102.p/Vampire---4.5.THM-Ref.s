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
% DateTime   : Thu Dec  3 13:20:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 147 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  239 ( 446 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f67,f75,f83,f94,f107,f111,f118,f127,f136,f143,f171,f192])).

fof(f192,plain,
    ( ~ spl2_5
    | ~ spl2_11
    | ~ spl2_24 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f93,f170,f66])).

fof(f66,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f170,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl2_24
  <=> v1_xboole_0(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f93,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_11
  <=> ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f171,plain,
    ( spl2_24
    | spl2_1
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f148,f140,f133,f125,f50,f45,f168])).

fof(f45,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f50,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f125,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f133,plain,
    ( spl2_18
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f140,plain,
    ( spl2_19
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f148,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f47,f52,f135,f142,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f125])).

fof(f142,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f140])).

fof(f135,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f52,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f143,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_19
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f113,f105,f60,f140,f55,f45])).

fof(f55,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f105,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f113,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f62,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f62,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f136,plain,
    ( spl2_18
    | spl2_1
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f123,f115,f109,f55,f45,f133])).

fof(f109,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f115,plain,
    ( spl2_16
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f123,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f119,f117])).

fof(f117,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f115])).

fof(f119,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f47,f57,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f57,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f127,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f36,f125])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f118,plain,
    ( spl2_16
    | spl2_1
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f112,f105,f55,f45,f115])).

fof(f112,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f47,f57,f106])).

fof(f111,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f43,f109])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f107,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f42,f105])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f94,plain,
    ( spl2_11
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f86,f81,f73,f92])).

fof(f73,plain,
    ( spl2_7
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f81,plain,
    ( spl2_9
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f86,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(superposition,[],[f82,f74])).

fof(f74,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f82,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f75,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f67,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f63,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f50])).

fof(f32,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f29,f45])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:04:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (17946)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (17956)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (17948)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (17946)Refutation not found, incomplete strategy% (17946)------------------------------
% 0.22/0.47  % (17946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17946)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (17946)Memory used [KB]: 1663
% 0.22/0.47  % (17946)Time elapsed: 0.051 s
% 0.22/0.47  % (17946)------------------------------
% 0.22/0.47  % (17946)------------------------------
% 0.22/0.47  % (17948)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f193,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f67,f75,f83,f94,f107,f111,f118,f127,f136,f143,f171,f192])).
% 0.22/0.47  fof(f192,plain,(
% 0.22/0.47    ~spl2_5 | ~spl2_11 | ~spl2_24),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.47  fof(f191,plain,(
% 0.22/0.47    $false | (~spl2_5 | ~spl2_11 | ~spl2_24)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f93,f170,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl2_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f170,plain,(
% 0.22/0.47    v1_xboole_0(k1_tarski(sK1)) | ~spl2_24),
% 0.22/0.47    inference(avatar_component_clause,[],[f168])).
% 0.22/0.47  fof(f168,plain,(
% 0.22/0.47    spl2_24 <=> v1_xboole_0(k1_tarski(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | ~spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    spl2_11 <=> ! [X0] : k1_xboole_0 != k1_tarski(X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    spl2_24 | spl2_1 | ~spl2_2 | ~spl2_17 | ~spl2_18 | ~spl2_19),
% 0.22/0.47    inference(avatar_split_clause,[],[f148,f140,f133,f125,f50,f45,f168])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl2_1 <=> v1_xboole_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    spl2_17 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    spl2_18 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    spl2_19 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    v1_xboole_0(k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_17 | ~spl2_18 | ~spl2_19)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f47,f52,f135,f142,f126])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f125])).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f140])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f133])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f50])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ~v1_xboole_0(sK0) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f45])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    spl2_1 | ~spl2_3 | spl2_19 | ~spl2_4 | ~spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f113,f105,f60,f140,f55,f45])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl2_14 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_14)),
% 0.22/0.47    inference(superposition,[],[f62,f106])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f105])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f60])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    spl2_18 | spl2_1 | ~spl2_3 | ~spl2_15 | ~spl2_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f123,f115,f109,f55,f45,f133])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    spl2_15 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    spl2_16 <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_15 | ~spl2_16)),
% 0.22/0.47    inference(forward_demodulation,[],[f119,f117])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | ~spl2_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f115])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_15)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f47,f57,f110])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f109])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f55])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl2_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f36,f125])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    spl2_16 | spl2_1 | ~spl2_3 | ~spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f112,f105,f55,f45,f115])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (spl2_1 | ~spl2_3 | ~spl2_14)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f47,f57,f106])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    spl2_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f43,f109])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f42,f105])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    spl2_11 | ~spl2_7 | ~spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f86,f81,f73,f92])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    spl2_7 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl2_9 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | (~spl2_7 | ~spl2_9)),
% 0.22/0.47    inference(superposition,[],[f82,f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f73])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl2_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f81])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f81])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f38,f73])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.47    inference(rectify,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f65])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f31,f60])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.47    inference(negated_conjecture,[],[f12])).
% 0.22/0.47  fof(f12,conjecture,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f30,f55])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    m1_subset_1(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f32,f50])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    v1_zfmisc_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f45])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ~v1_xboole_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (17948)------------------------------
% 0.22/0.47  % (17948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17948)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (17948)Memory used [KB]: 6140
% 0.22/0.47  % (17948)Time elapsed: 0.055 s
% 0.22/0.47  % (17948)------------------------------
% 0.22/0.47  % (17948)------------------------------
% 0.22/0.47  % (17945)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (17942)Success in time 0.109 s
%------------------------------------------------------------------------------
