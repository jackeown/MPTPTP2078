%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:17 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 136 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  214 ( 386 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f70,f76,f84,f95,f103,f110,f118])).

fof(f118,plain,(
    ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f116,f31])).

fof(f31,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f116,plain,
    ( sK1 = k1_ordinal1(sK1)
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f115,f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f115,plain,
    ( k1_ordinal1(sK1) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_11 ),
    inference(superposition,[],[f34,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_11
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f34,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f110,plain,
    ( spl2_11
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f105,f100,f107])).

fof(f100,plain,
    ( spl2_10
  <=> v1_xboole_0(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f105,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl2_10 ),
    inference(resolution,[],[f102,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f102,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f98,f81,f73,f49,f100])).

fof(f49,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f73,plain,
    ( spl2_6
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f81,plain,
    ( spl2_7
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f98,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f97,f75])).

fof(f75,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f97,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f96,f83])).

fof(f83,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f95,plain,
    ( spl2_8
    | spl2_9
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f85,f81,f92,f88])).

fof(f88,plain,
    ( spl2_8
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f92,plain,
    ( spl2_9
  <=> m1_subset_1(k6_domain_1(k1_zfmisc_1(sK0),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f85,plain,
    ( m1_subset_1(k6_domain_1(k1_zfmisc_1(sK0),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl2_7 ),
    inference(resolution,[],[f83,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f84,plain,
    ( spl2_7
    | spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f79,f67,f54,f44,f81])).

fof(f44,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f54,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( spl2_5
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f79,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f78,f69])).

fof(f69,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f78,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f77,f46])).

fof(f46,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f77,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f76,plain,
    ( spl2_6
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f71,f67,f59,f73])).

fof(f59,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f71,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f61,f69])).

fof(f61,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f70,plain,
    ( spl2_5
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f65,f54,f44,f67])).

fof(f65,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f64,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f40,f56])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f57,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f44])).

fof(f27,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:44:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.43  % (28402)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.48  % (28412)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.48  % (28407)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (28402)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f119,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f70,f76,f84,f95,f103,f110,f118])).
% 0.23/0.48  fof(f118,plain,(
% 0.23/0.48    ~spl2_11),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f117])).
% 0.23/0.48  fof(f117,plain,(
% 0.23/0.48    $false | ~spl2_11),
% 0.23/0.48    inference(subsumption_resolution,[],[f116,f31])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,axiom,(
% 0.23/0.48    ! [X0] : k1_ordinal1(X0) != X0),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 0.23/0.48  fof(f116,plain,(
% 0.23/0.48    sK1 = k1_ordinal1(sK1) | ~spl2_11),
% 0.23/0.48    inference(forward_demodulation,[],[f115,f32])).
% 0.23/0.48  fof(f32,plain,(
% 0.23/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.48  fof(f115,plain,(
% 0.23/0.48    k1_ordinal1(sK1) = k2_xboole_0(sK1,k1_xboole_0) | ~spl2_11),
% 0.23/0.48    inference(superposition,[],[f34,f109])).
% 0.23/0.48  fof(f109,plain,(
% 0.23/0.48    k1_xboole_0 = k1_tarski(sK1) | ~spl2_11),
% 0.23/0.48    inference(avatar_component_clause,[],[f107])).
% 0.23/0.48  fof(f107,plain,(
% 0.23/0.48    spl2_11 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.23/0.48  fof(f34,plain,(
% 0.23/0.48    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.23/0.48  fof(f110,plain,(
% 0.23/0.48    spl2_11 | ~spl2_10),
% 0.23/0.48    inference(avatar_split_clause,[],[f105,f100,f107])).
% 0.23/0.48  fof(f100,plain,(
% 0.23/0.48    spl2_10 <=> v1_xboole_0(k1_tarski(sK1))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.48  fof(f105,plain,(
% 0.23/0.48    k1_xboole_0 = k1_tarski(sK1) | ~spl2_10),
% 0.23/0.48    inference(resolution,[],[f102,f35])).
% 0.23/0.48  fof(f35,plain,(
% 0.23/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f16])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.23/0.48  fof(f102,plain,(
% 0.23/0.48    v1_xboole_0(k1_tarski(sK1)) | ~spl2_10),
% 0.23/0.48    inference(avatar_component_clause,[],[f100])).
% 0.23/0.48  fof(f103,plain,(
% 0.23/0.48    spl2_10 | ~spl2_2 | ~spl2_6 | ~spl2_7),
% 0.23/0.48    inference(avatar_split_clause,[],[f98,f81,f73,f49,f100])).
% 0.23/0.48  fof(f49,plain,(
% 0.23/0.48    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.49  fof(f73,plain,(
% 0.23/0.49    spl2_6 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.49  fof(f81,plain,(
% 0.23/0.49    spl2_7 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.23/0.49  fof(f98,plain,(
% 0.23/0.49    v1_xboole_0(k1_tarski(sK1)) | (~spl2_2 | ~spl2_6 | ~spl2_7)),
% 0.23/0.49    inference(subsumption_resolution,[],[f97,f75])).
% 0.23/0.49  fof(f75,plain,(
% 0.23/0.49    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_6),
% 0.23/0.49    inference(avatar_component_clause,[],[f73])).
% 0.23/0.49  fof(f97,plain,(
% 0.23/0.49    v1_xboole_0(k1_tarski(sK1)) | ~v1_subset_1(k1_tarski(sK1),sK0) | (~spl2_2 | ~spl2_7)),
% 0.23/0.49    inference(resolution,[],[f96,f83])).
% 0.23/0.49  fof(f83,plain,(
% 0.23/0.49    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_7),
% 0.23/0.49    inference(avatar_component_clause,[],[f81])).
% 0.23/0.49  fof(f96,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | ~v1_subset_1(X0,sK0)) ) | ~spl2_2),
% 0.23/0.49    inference(resolution,[],[f42,f51])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.23/0.49    inference(avatar_component_clause,[],[f49])).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f37,f36])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.23/0.49    inference(flattening,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f11])).
% 0.23/0.49  fof(f11,axiom,(
% 0.23/0.49    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.23/0.49  fof(f95,plain,(
% 0.23/0.49    spl2_8 | spl2_9 | ~spl2_7),
% 0.23/0.49    inference(avatar_split_clause,[],[f85,f81,f92,f88])).
% 0.23/0.49  fof(f88,plain,(
% 0.23/0.49    spl2_8 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.23/0.49  fof(f92,plain,(
% 0.23/0.49    spl2_9 <=> m1_subset_1(k6_domain_1(k1_zfmisc_1(sK0),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.23/0.49  fof(f85,plain,(
% 0.23/0.49    m1_subset_1(k6_domain_1(k1_zfmisc_1(sK0),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl2_7),
% 0.23/0.49    inference(resolution,[],[f83,f41])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.23/0.49    inference(flattening,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,axiom,(
% 0.23/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.23/0.49  fof(f84,plain,(
% 0.23/0.49    spl2_7 | spl2_1 | ~spl2_3 | ~spl2_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f79,f67,f54,f44,f81])).
% 0.23/0.49  fof(f44,plain,(
% 0.23/0.49    spl2_1 <=> v1_xboole_0(sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.49  fof(f67,plain,(
% 0.23/0.49    spl2_5 <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.49  fof(f79,plain,(
% 0.23/0.49    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_5)),
% 0.23/0.49    inference(forward_demodulation,[],[f78,f69])).
% 0.23/0.49  fof(f69,plain,(
% 0.23/0.49    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | ~spl2_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f67])).
% 0.23/0.49  fof(f78,plain,(
% 0.23/0.49    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3)),
% 0.23/0.49    inference(subsumption_resolution,[],[f77,f46])).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ~v1_xboole_0(sK0) | spl2_1),
% 0.23/0.49    inference(avatar_component_clause,[],[f44])).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0) | ~spl2_3),
% 0.23/0.49    inference(resolution,[],[f41,f56])).
% 0.23/0.49  fof(f56,plain,(
% 0.23/0.49    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.23/0.49    inference(avatar_component_clause,[],[f54])).
% 0.23/0.49  fof(f76,plain,(
% 0.23/0.49    spl2_6 | ~spl2_4 | ~spl2_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f71,f67,f59,f73])).
% 0.23/0.49  fof(f59,plain,(
% 0.23/0.49    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.49  fof(f71,plain,(
% 0.23/0.49    v1_subset_1(k1_tarski(sK1),sK0) | (~spl2_4 | ~spl2_5)),
% 0.23/0.49    inference(superposition,[],[f61,f69])).
% 0.23/0.49  fof(f61,plain,(
% 0.23/0.49    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.23/0.49    inference(avatar_component_clause,[],[f59])).
% 0.23/0.49  fof(f70,plain,(
% 0.23/0.49    spl2_5 | spl2_1 | ~spl2_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f65,f54,f44,f67])).
% 0.23/0.49  fof(f65,plain,(
% 0.23/0.49    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (spl2_1 | ~spl2_3)),
% 0.23/0.49    inference(subsumption_resolution,[],[f64,f46])).
% 0.23/0.49  fof(f64,plain,(
% 0.23/0.49    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | v1_xboole_0(sK0) | ~spl2_3),
% 0.23/0.49    inference(resolution,[],[f40,f56])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.23/0.49    inference(flattening,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,axiom,(
% 0.23/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.23/0.49  fof(f62,plain,(
% 0.23/0.49    spl2_4),
% 0.23/0.49    inference(avatar_split_clause,[],[f29,f59])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.23/0.49    inference(flattening,[],[f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,negated_conjecture,(
% 0.23/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.23/0.49    inference(negated_conjecture,[],[f12])).
% 0.23/0.49  fof(f12,conjecture,(
% 0.23/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.23/0.49  fof(f57,plain,(
% 0.23/0.49    spl2_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f28,f54])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    m1_subset_1(sK1,sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f26])).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    spl2_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f30,f49])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    v1_zfmisc_1(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f26])).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ~spl2_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f27,f44])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ~v1_xboole_0(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f26])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (28402)------------------------------
% 0.23/0.49  % (28402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (28402)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (28402)Memory used [KB]: 6140
% 0.23/0.49  % (28402)Time elapsed: 0.061 s
% 0.23/0.49  % (28402)------------------------------
% 0.23/0.49  % (28402)------------------------------
% 0.23/0.49  % (28401)Success in time 0.116 s
%------------------------------------------------------------------------------
