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
% DateTime   : Thu Dec  3 13:20:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 117 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  215 ( 395 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f63,f79,f83,f90,f102,f113,f120,f128])).

fof(f128,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f58,f121])).

fof(f121,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_1
    | ~ spl2_17 ),
    inference(superposition,[],[f38,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f38,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f58,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f120,plain,
    ( spl2_17
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f114,f111,f99,f61,f46,f41,f36,f117])).

fof(f41,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f46,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f61,plain,
    ( spl2_6
  <=> ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f99,plain,
    ( spl2_14
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f111,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( v1_xboole_0(k1_tarski(X0))
        | ~ v1_subset_1(k1_tarski(X0),X1)
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f38,f43,f48,f62,f101,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(k1_tarski(X0),X1)
        | v1_xboole_0(k1_tarski(X0))
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f101,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f62,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_tarski(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f48,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f43,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f113,plain,
    ( spl2_16
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f91,f88,f77,f111])).

fof(f77,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f88,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_tarski(X0))
        | ~ v1_subset_1(k1_tarski(X0),X1)
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,X1) )
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(resolution,[],[f89,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f102,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_14
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f86,f81,f51,f99,f46,f36])).

fof(f51,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f81,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k1_tarski(X1) = k6_domain_1(X0,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f86,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(superposition,[],[f53,f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X1) = k6_domain_1(X0,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f53,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f90,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f31,f88])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f83,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f34,f81])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f79,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f63,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f49,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (9382)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (9387)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (9389)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (9382)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f63,f79,f83,f90,f102,f113,f120,f128])).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    spl2_1 | ~spl2_5 | ~spl2_17),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    $false | (spl2_1 | ~spl2_5 | ~spl2_17)),
% 0.22/0.47    inference(subsumption_resolution,[],[f58,f121])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | (spl2_1 | ~spl2_17)),
% 0.22/0.47    inference(superposition,[],[f38,f119])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | ~spl2_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f117])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl2_17 <=> k1_xboole_0 = sK0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ~v1_xboole_0(sK0) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl2_1 <=> v1_xboole_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl2_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    spl2_17 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_14 | ~spl2_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f114,f111,f99,f61,f46,f41,f36,f117])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl2_6 <=> ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl2_14 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    spl2_16 <=> ! [X1,X0] : (v1_xboole_0(k1_tarski(X0)) | ~v1_subset_1(k1_tarski(X0),X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_14 | ~spl2_16)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f38,f43,f48,f62,f101,f112])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_subset_1(k1_tarski(X0),X1) | v1_xboole_0(k1_tarski(X0)) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1)) ) | ~spl2_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f111])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f99])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) ) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f61])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f46])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f41])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    spl2_16 | ~spl2_10 | ~spl2_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f91,f88,f77,f111])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl2_10 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl2_12 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_xboole_0(k1_tarski(X0)) | ~v1_subset_1(k1_tarski(X0),X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1)) ) | (~spl2_10 | ~spl2_12)),
% 0.22/0.47    inference(resolution,[],[f89,f78])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) ) | ~spl2_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f88])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    spl2_1 | ~spl2_3 | spl2_14 | ~spl2_4 | ~spl2_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f86,f81,f51,f99,f46,f36])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl2_11 <=> ! [X1,X0] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_11)),
% 0.22/0.47    inference(superposition,[],[f53,f82])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f81])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl2_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f31,f88])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    spl2_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f81])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f33,f77])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f61])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f27,f56])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f51])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.47    inference(negated_conjecture,[],[f9])).
% 0.22/0.47  fof(f9,conjecture,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f46])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    m1_subset_1(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f41])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    v1_zfmisc_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f36])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ~v1_xboole_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (9382)------------------------------
% 0.22/0.47  % (9382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (9382)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (9382)Memory used [KB]: 6140
% 0.22/0.47  % (9382)Time elapsed: 0.063 s
% 0.22/0.47  % (9382)------------------------------
% 0.22/0.47  % (9382)------------------------------
% 0.22/0.48  % (9376)Success in time 0.113 s
%------------------------------------------------------------------------------
