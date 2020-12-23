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
% DateTime   : Thu Dec  3 13:20:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 139 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  230 ( 429 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f63,f71,f76,f94,f99,f103,f114,f128,f135,f172,f187])).

fof(f187,plain,
    ( ~ spl2_5
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f93,f171,f62])).

fof(f62,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f171,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl2_24
  <=> v1_xboole_0(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f93,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_12
  <=> ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f172,plain,
    ( spl2_24
    | spl2_1
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f145,f132,f125,f112,f46,f41,f169])).

fof(f41,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f112,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f125,plain,
    ( spl2_17
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f132,plain,
    ( spl2_18
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f145,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f43,f48,f127,f134,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f112])).

fof(f134,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f127,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f125])).

fof(f48,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f43,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f135,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_18
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f105,f97,f56,f132,f51,f41])).

fof(f51,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f56,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f97,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f105,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(superposition,[],[f58,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f58,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f128,plain,
    ( spl2_17
    | spl2_1
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f110,f101,f97,f51,f41,f125])).

fof(f101,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f110,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f106,f104])).

fof(f104,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f43,f53,f98])).

fof(f53,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f106,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f43,f53,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f114,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f33,f112])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f103,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f39,f101])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f99,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f94,plain,
    ( spl2_12
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f90,f74,f69,f92])).

fof(f69,plain,
    ( spl2_7
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f74,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f90,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(superposition,[],[f70,f75])).

fof(f75,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f70,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f71,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f63,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f54,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (28144)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (28144)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f190,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f63,f71,f76,f94,f99,f103,f114,f128,f135,f172,f187])).
% 0.20/0.45  fof(f187,plain,(
% 0.20/0.45    ~spl2_5 | ~spl2_12 | ~spl2_24),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f186])).
% 0.20/0.45  fof(f186,plain,(
% 0.20/0.45    $false | (~spl2_5 | ~spl2_12 | ~spl2_24)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f93,f171,f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl2_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f61])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    spl2_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    v1_xboole_0(k1_tarski(sK1)) | ~spl2_24),
% 0.20/0.45    inference(avatar_component_clause,[],[f169])).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    spl2_24 <=> v1_xboole_0(k1_tarski(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | ~spl2_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f92])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    spl2_12 <=> ! [X0] : k1_xboole_0 != k1_tarski(X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    spl2_24 | spl2_1 | ~spl2_2 | ~spl2_15 | ~spl2_17 | ~spl2_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f145,f132,f125,f112,f46,f41,f169])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    spl2_1 <=> v1_xboole_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    spl2_15 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    spl2_17 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    spl2_18 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.45  fof(f145,plain,(
% 0.20/0.45    v1_xboole_0(k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_15 | ~spl2_17 | ~spl2_18)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f43,f48,f127,f134,f113])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_15),
% 0.20/0.45    inference(avatar_component_clause,[],[f112])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_18),
% 0.20/0.45    inference(avatar_component_clause,[],[f132])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_17),
% 0.20/0.45    inference(avatar_component_clause,[],[f125])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f46])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ~v1_xboole_0(sK0) | spl2_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f41])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    spl2_1 | ~spl2_3 | spl2_18 | ~spl2_4 | ~spl2_13),
% 0.20/0.45    inference(avatar_split_clause,[],[f105,f97,f56,f132,f51,f41])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    spl2_13 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_13)),
% 0.20/0.45    inference(superposition,[],[f58,f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_13),
% 0.20/0.45    inference(avatar_component_clause,[],[f97])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f56])).
% 0.20/0.45  fof(f128,plain,(
% 0.20/0.45    spl2_17 | spl2_1 | ~spl2_3 | ~spl2_13 | ~spl2_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f110,f101,f97,f51,f41,f125])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    spl2_14 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_13 | ~spl2_14)),
% 0.20/0.45    inference(forward_demodulation,[],[f106,f104])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (spl2_1 | ~spl2_3 | ~spl2_13)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f43,f53,f98])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f51])).
% 0.20/0.45  fof(f106,plain,(
% 0.20/0.45    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_14)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f43,f53,f102])).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f101])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    spl2_15),
% 0.20/0.45    inference(avatar_split_clause,[],[f33,f112])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    spl2_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f39,f101])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    spl2_13),
% 0.20/0.45    inference(avatar_split_clause,[],[f38,f97])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    spl2_12 | ~spl2_7 | ~spl2_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f90,f74,f69,f92])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    spl2_7 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | (~spl2_7 | ~spl2_8)),
% 0.20/0.45    inference(superposition,[],[f70,f75])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f74])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl2_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f69])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    spl2_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f35,f74])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    spl2_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f34,f69])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    spl2_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f31,f61])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl2_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f28,f56])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.45    inference(negated_conjecture,[],[f11])).
% 0.20/0.45  fof(f11,conjecture,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    spl2_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f27,f51])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    m1_subset_1(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    spl2_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f29,f46])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    v1_zfmisc_1(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ~spl2_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f26,f41])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ~v1_xboole_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (28144)------------------------------
% 0.20/0.45  % (28144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (28144)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (28144)Memory used [KB]: 6140
% 0.20/0.45  % (28144)Time elapsed: 0.057 s
% 0.20/0.45  % (28144)------------------------------
% 0.20/0.45  % (28144)------------------------------
% 0.20/0.45  % (28132)Success in time 0.099 s
%------------------------------------------------------------------------------
