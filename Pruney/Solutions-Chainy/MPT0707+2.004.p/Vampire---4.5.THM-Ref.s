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
% DateTime   : Thu Dec  3 12:54:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 128 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 285 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f44,f52,f56,f60,f68,f76,f84,f90,f94,f108,f112,f120,f126,f132,f151])).

fof(f151,plain,
    ( ~ spl2_15
    | spl2_18
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl2_15
    | spl2_18
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f125,f143])).

fof(f143,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(superposition,[],[f131,f107])).

fof(f107,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_15
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f131,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_19
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f125,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_18
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f132,plain,
    ( spl2_19
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f115,f110,f66,f130])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f110,plain,
    ( spl2_16
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f115,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(superposition,[],[f111,f67])).

fof(f67,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f111,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f126,plain,
    ( ~ spl2_18
    | spl2_2
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f121,f118,f37,f123])).

fof(f37,plain,
    ( spl2_2
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f118,plain,
    ( spl2_17
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f121,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_2
    | ~ spl2_17 ),
    inference(superposition,[],[f39,f119])).

fof(f119,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f39,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f120,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f99,f92,f88,f50,f42,f118])).

fof(f42,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f88,plain,
    ( spl2_13
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f92,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f99,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f98,f51])).

fof(f51,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f98,plain,
    ( ! [X0,X1] : k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f97,f89])).

fof(f89,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f97,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f95,f51])).

fof(f95,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f43,f43,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f112,plain,
    ( spl2_16
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f85,f66,f54,f110])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f85,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f67,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f108,plain,
    ( spl2_15
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f102,f81,f74,f105])).

fof(f74,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f81,plain,
    ( spl2_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

% (14018)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f102,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f83,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f83,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f94,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f23,f92])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f90,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f27,f88])).

fof(f27,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f84,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f77,f58,f32,f81])).

fof(f32,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f77,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f34,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f76,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f35,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:04:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (14007)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (14008)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (14008)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f35,f40,f44,f52,f56,f60,f68,f76,f84,f90,f94,f108,f112,f120,f126,f132,f151])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    ~spl2_15 | spl2_18 | ~spl2_19),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f150])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    $false | (~spl2_15 | spl2_18 | ~spl2_19)),
% 0.22/0.47    inference(subsumption_resolution,[],[f125,f143])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_15 | ~spl2_19)),
% 0.22/0.47    inference(superposition,[],[f131,f107])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl2_15 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl2_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f130])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    spl2_19 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    sK1 != k3_xboole_0(sK0,sK1) | spl2_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f123])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    spl2_18 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    spl2_19 | ~spl2_9 | ~spl2_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f115,f110,f66,f130])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl2_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    spl2_16 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_9 | ~spl2_16)),
% 0.22/0.47    inference(superposition,[],[f111,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl2_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f66])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f110])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    ~spl2_18 | spl2_2 | ~spl2_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f121,f118,f37,f123])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl2_2 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    spl2_17 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    sK1 != k3_xboole_0(sK0,sK1) | (spl2_2 | ~spl2_17)),
% 0.22/0.47    inference(superposition,[],[f39,f119])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f118])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f37])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    spl2_17 | ~spl2_3 | ~spl2_5 | ~spl2_13 | ~spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f99,f92,f88,f50,f42,f118])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl2_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl2_13 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    spl2_14 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_13 | ~spl2_14)),
% 0.22/0.47    inference(forward_demodulation,[],[f98,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f50])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_13 | ~spl2_14)),
% 0.22/0.47    inference(forward_demodulation,[],[f97,f89])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f88])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_14)),
% 0.22/0.47    inference(forward_demodulation,[],[f95,f51])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) ) | (~spl2_3 | ~spl2_14)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f43,f43,f93])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f92])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f42])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    spl2_16 | ~spl2_6 | ~spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f85,f66,f54,f110])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl2_6 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_6 | ~spl2_9)),
% 0.22/0.47    inference(superposition,[],[f67,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f54])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl2_15 | ~spl2_11 | ~spl2_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f102,f81,f74,f105])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    spl2_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl2_12 <=> r1_tarski(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.47  % (14018)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_11 | ~spl2_12)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f83,f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f74])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    r1_tarski(sK1,sK0) | ~spl2_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f81])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f92])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl2_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f27,f88])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl2_12 | ~spl2_1 | ~spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f77,f58,f32,f81])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl2_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    r1_tarski(sK1,sK0) | (~spl2_1 | ~spl2_7)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f34,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f58])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl2_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f74])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f66])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f58])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.47    inference(nnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f54])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f50])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ~spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f19,f37])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.47    inference(negated_conjecture,[],[f10])).
% 0.22/0.47  fof(f10,conjecture,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f32])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (14008)------------------------------
% 0.22/0.47  % (14008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (14008)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (14008)Memory used [KB]: 6140
% 0.22/0.47  % (14008)Time elapsed: 0.063 s
% 0.22/0.47  % (14008)------------------------------
% 0.22/0.47  % (14008)------------------------------
% 0.22/0.47  % (14005)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (14002)Success in time 0.114 s
%------------------------------------------------------------------------------
