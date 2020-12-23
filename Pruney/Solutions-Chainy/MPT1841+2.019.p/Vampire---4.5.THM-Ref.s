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
% DateTime   : Thu Dec  3 13:20:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 123 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 355 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f71,f73,f100,f129,f131,f187])).

fof(f187,plain,(
    ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl2_9 ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_9 ),
    inference(superposition,[],[f178,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl2_9 ),
    inference(resolution,[],[f113,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f113,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_9
  <=> v1_xboole_0(k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f178,plain,(
    ! [X0] : k1_xboole_0 != k2_tarski(X0,X0) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f37,f43,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f131,plain,
    ( ~ spl2_4
    | spl2_9
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f130,f127,f57,f111,f68])).

fof(f68,plain,
    ( spl2_4
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f57,plain,
    ( spl2_2
  <=> k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f127,plain,
    ( spl2_11
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f130,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),sK0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f30,f59])).

fof(f59,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f30,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f128,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( spl2_1
    | spl2_11 ),
    inference(avatar_split_clause,[],[f103,f127,f53])).

fof(f53,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f103,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
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

fof(f100,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f55,f28])).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f73,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f66,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f71,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f62,f57,f68,f64,f53])).

fof(f62,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f41,f59])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
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

fof(f60,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f50,f57,f53])).

fof(f50,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f46,f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

% (10809)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (10813)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (10807)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (10807)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f60,f71,f73,f100,f129,f131,f187])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    ~spl2_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    $false | ~spl2_9),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f185])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | ~spl2_9),
% 0.21/0.47    inference(superposition,[],[f178,f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl2_9),
% 0.21/0.47    inference(resolution,[],[f113,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(resolution,[],[f42,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    v1_xboole_0(k2_tarski(sK1,sK1)) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl2_9 <=> v1_xboole_0(k2_tarski(sK1,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k2_tarski(X0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f45,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f36,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f39,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    inference(rectify,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f37,f43,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~spl2_4 | spl2_9 | ~spl2_2 | ~spl2_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f127,f57,f111,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl2_4 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl2_2 <=> k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl2_11 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    v1_xboole_0(k2_tarski(sK1,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK0)) | (~spl2_2 | ~spl2_11)),
% 0.21/0.47    inference(resolution,[],[f128,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    v1_subset_1(k2_tarski(sK1,sK1),sK0) | ~spl2_2),
% 0.21/0.47    inference(backward_demodulation,[],[f30,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_subset_1(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl2_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f127])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl2_1 | spl2_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f103,f127,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl2_1 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.47    inference(resolution,[],[f35,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    v1_zfmisc_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    $false | ~spl2_1),
% 0.21/0.47    inference(resolution,[],[f55,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    $false | spl2_3),
% 0.21/0.47    inference(resolution,[],[f66,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,sK0) | spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl2_1 | ~spl2_3 | spl2_4 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f57,f68,f64,f53])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | ~spl2_2),
% 0.21/0.47    inference(superposition,[],[f41,f59])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f57,f53])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f46,f29])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f40,f33])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  % (10809)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (10807)------------------------------
% 0.21/0.47  % (10807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (10807)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (10807)Memory used [KB]: 6140
% 0.21/0.47  % (10807)Time elapsed: 0.043 s
% 0.21/0.47  % (10807)------------------------------
% 0.21/0.47  % (10807)------------------------------
% 0.21/0.47  % (10800)Success in time 0.11 s
%------------------------------------------------------------------------------
