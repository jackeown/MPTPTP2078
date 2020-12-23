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
% DateTime   : Thu Dec  3 13:20:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 125 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 350 expanded)
%              Number of equality atoms :   30 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f64,f70,f72,f93,f97,f102])).

fof(f102,plain,(
    ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_6 ),
    inference(superposition,[],[f84,f92])).

% (17760)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f92,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_6
  <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f44,f43])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f36,f41,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f97,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    ~ v1_xboole_0(sK0) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f50,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f93,plain,
    ( spl2_1
    | spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f88,f61,f90,f48])).

fof(f61,plain,
    ( spl2_4
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f88,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f85,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f63,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f63,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f85,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,(
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

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f72,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f69,f28])).

fof(f69,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f70,plain,
    ( spl2_1
    | ~ spl2_5
    | spl2_3 ),
    inference(avatar_split_clause,[],[f65,f57,f67,f48])).

fof(f57,plain,
    ( spl2_3
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | spl2_3 ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f59,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f55,f52,f61,f57])).

fof(f52,plain,
    ( spl2_2
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f55,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f53,f29])).

fof(f29,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f46,f52,f48])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (17754)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (17752)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (17752)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (17759)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (17753)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (17753)Refutation not found, incomplete strategy% (17753)------------------------------
% 0.22/0.47  % (17753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17753)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (17753)Memory used [KB]: 1663
% 0.22/0.47  % (17753)Time elapsed: 0.005 s
% 0.22/0.47  % (17753)------------------------------
% 0.22/0.47  % (17753)------------------------------
% 0.22/0.47  % (17751)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f54,f64,f70,f72,f93,f97,f102])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    ~spl2_6),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    $false | ~spl2_6),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0 | ~spl2_6),
% 0.22/0.47    inference(superposition,[],[f84,f92])).
% 0.22/0.47  % (17760)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f90])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl2_6 <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.22/0.47    inference(superposition,[],[f44,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f35,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f37,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.47    inference(rectify,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f36,f41,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f31,f38])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    $false | ~spl2_1),
% 0.22/0.47    inference(resolution,[],[f50,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ~v1_xboole_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.47    inference(negated_conjecture,[],[f11])).
% 0.22/0.47  fof(f11,conjecture,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    v1_xboole_0(sK0) | ~spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl2_1 <=> v1_xboole_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl2_1 | spl2_6 | ~spl2_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f88,f61,f90,f48])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl2_4 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | v1_xboole_0(sK0) | ~spl2_4),
% 0.22/0.48    inference(forward_demodulation,[],[f85,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    k1_xboole_0 = k6_domain_1(sK0,sK1) | ~spl2_4),
% 0.22/0.48    inference(resolution,[],[f63,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | v1_xboole_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f45,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    m1_subset_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f39,f42])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl2_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    $false | spl2_5),
% 0.22/0.48    inference(resolution,[],[f69,f28])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,sK0) | spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl2_5 <=> m1_subset_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl2_1 | ~spl2_5 | spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f65,f57,f67,f48])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl2_3 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | spl2_3),
% 0.22/0.48    inference(resolution,[],[f59,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ~spl2_3 | spl2_4 | ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f55,f52,f61,f57])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl2_2 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.48    inference(resolution,[],[f53,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_subset_1(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f52])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl2_1 | spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f46,f52,f48])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f34,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    v1_zfmisc_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (17752)------------------------------
% 0.22/0.48  % (17752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17752)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (17752)Memory used [KB]: 6140
% 0.22/0.48  % (17752)Time elapsed: 0.055 s
% 0.22/0.48  % (17752)------------------------------
% 0.22/0.48  % (17752)------------------------------
% 0.22/0.48  % (17756)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (17748)Success in time 0.117 s
%------------------------------------------------------------------------------
