%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:32 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 111 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :  186 ( 272 expanded)
%              Number of equality atoms :   46 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f50,f54,f62,f66,f70,f78,f85,f90,f95,f102,f108,f112])).

fof(f112,plain,
    ( spl2_1
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl2_1
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f32,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f110,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f109,f53])).

fof(f53,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_6
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f109,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(superposition,[],[f94,f107])).

fof(f107,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_17
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f94,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_15
  <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f108,plain,
    ( spl2_17
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f103,f100,f82,f105])).

fof(f82,plain,
    ( spl2_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f100,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f103,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(resolution,[],[f101,f84])).

fof(f84,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f98,f88,f68,f52,f48,f100])).

fof(f48,plain,
    ( spl2_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f68,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f88,plain,
    ( spl2_14
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f97,f89])).

fof(f89,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f88])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f96,f53])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f69,f49])).

fof(f49,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f95,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f91,f64,f48,f93])).

fof(f64,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f91,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f90,plain,
    ( spl2_14
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f86,f60,f48,f88])).

fof(f60,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f86,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f61,f49])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f85,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f79,f76,f35,f82])).

fof(f35,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f79,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(resolution,[],[f77,f37])).

fof(f37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f27,f76])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f66,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f62,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f54,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f30])).

fof(f18,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.40  % (28645)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.14/0.41  % (28643)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.41  % (28644)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.41  % (28643)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.14/0.41  % SZS output start Proof for theBenchmark
% 0.14/0.41  fof(f113,plain,(
% 0.14/0.41    $false),
% 0.14/0.41    inference(avatar_sat_refutation,[],[f33,f38,f50,f54,f62,f66,f70,f78,f85,f90,f95,f102,f108,f112])).
% 0.14/0.41  fof(f112,plain,(
% 0.14/0.41    spl2_1 | ~spl2_6 | ~spl2_15 | ~spl2_17),
% 0.14/0.41    inference(avatar_contradiction_clause,[],[f111])).
% 0.14/0.41  fof(f111,plain,(
% 0.14/0.41    $false | (spl2_1 | ~spl2_6 | ~spl2_15 | ~spl2_17)),
% 0.14/0.41    inference(subsumption_resolution,[],[f110,f32])).
% 0.14/0.41  fof(f32,plain,(
% 0.14/0.41    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.14/0.41    inference(avatar_component_clause,[],[f30])).
% 0.14/0.41  fof(f30,plain,(
% 0.14/0.41    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.14/0.41  fof(f110,plain,(
% 0.14/0.41    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | (~spl2_6 | ~spl2_15 | ~spl2_17)),
% 0.14/0.41    inference(forward_demodulation,[],[f109,f53])).
% 0.14/0.41  fof(f53,plain,(
% 0.14/0.41    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.14/0.41    inference(avatar_component_clause,[],[f52])).
% 0.14/0.41  fof(f52,plain,(
% 0.14/0.41    spl2_6 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.14/0.41  fof(f109,plain,(
% 0.14/0.41    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) | (~spl2_15 | ~spl2_17)),
% 0.14/0.41    inference(superposition,[],[f94,f107])).
% 0.14/0.41  fof(f107,plain,(
% 0.14/0.41    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl2_17),
% 0.14/0.41    inference(avatar_component_clause,[],[f105])).
% 0.14/0.41  fof(f105,plain,(
% 0.14/0.41    spl2_17 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.14/0.41  fof(f94,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_15),
% 0.14/0.41    inference(avatar_component_clause,[],[f93])).
% 0.14/0.41  fof(f93,plain,(
% 0.14/0.41    spl2_15 <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.14/0.41  fof(f108,plain,(
% 0.14/0.41    spl2_17 | ~spl2_13 | ~spl2_16),
% 0.14/0.41    inference(avatar_split_clause,[],[f103,f100,f82,f105])).
% 0.14/0.41  fof(f82,plain,(
% 0.14/0.41    spl2_13 <=> r1_tarski(sK1,sK0)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.14/0.41  fof(f100,plain,(
% 0.14/0.41    spl2_16 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.14/0.41  fof(f103,plain,(
% 0.14/0.41    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_13 | ~spl2_16)),
% 0.14/0.41    inference(resolution,[],[f101,f84])).
% 0.14/0.41  fof(f84,plain,(
% 0.14/0.41    r1_tarski(sK1,sK0) | ~spl2_13),
% 0.14/0.41    inference(avatar_component_clause,[],[f82])).
% 0.14/0.41  fof(f101,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_16),
% 0.14/0.41    inference(avatar_component_clause,[],[f100])).
% 0.14/0.41  fof(f102,plain,(
% 0.14/0.41    spl2_16 | ~spl2_5 | ~spl2_6 | ~spl2_10 | ~spl2_14),
% 0.14/0.41    inference(avatar_split_clause,[],[f98,f88,f68,f52,f48,f100])).
% 0.14/0.41  fof(f48,plain,(
% 0.14/0.41    spl2_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.14/0.41  fof(f68,plain,(
% 0.14/0.41    spl2_10 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.14/0.41  fof(f88,plain,(
% 0.14/0.41    spl2_14 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.14/0.41  fof(f98,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) ) | (~spl2_5 | ~spl2_6 | ~spl2_10 | ~spl2_14)),
% 0.14/0.41    inference(forward_demodulation,[],[f97,f89])).
% 0.14/0.41  fof(f89,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | ~spl2_14),
% 0.14/0.41    inference(avatar_component_clause,[],[f88])).
% 0.14/0.41  fof(f97,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_5 | ~spl2_6 | ~spl2_10)),
% 0.14/0.41    inference(forward_demodulation,[],[f96,f53])).
% 0.14/0.41  fof(f96,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_5 | ~spl2_10)),
% 0.14/0.41    inference(resolution,[],[f69,f49])).
% 0.14/0.41  fof(f49,plain,(
% 0.14/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_5),
% 0.14/0.41    inference(avatar_component_clause,[],[f48])).
% 0.14/0.41  fof(f69,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl2_10),
% 0.14/0.41    inference(avatar_component_clause,[],[f68])).
% 0.14/0.41  fof(f95,plain,(
% 0.14/0.41    spl2_15 | ~spl2_5 | ~spl2_9),
% 0.14/0.41    inference(avatar_split_clause,[],[f91,f64,f48,f93])).
% 0.14/0.41  fof(f64,plain,(
% 0.14/0.41    spl2_9 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.14/0.41  fof(f91,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_5 | ~spl2_9)),
% 0.14/0.41    inference(resolution,[],[f65,f49])).
% 0.14/0.41  fof(f65,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_9),
% 0.14/0.41    inference(avatar_component_clause,[],[f64])).
% 0.14/0.41  fof(f90,plain,(
% 0.14/0.41    spl2_14 | ~spl2_5 | ~spl2_8),
% 0.14/0.41    inference(avatar_split_clause,[],[f86,f60,f48,f88])).
% 0.14/0.41  fof(f60,plain,(
% 0.14/0.41    spl2_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.14/0.41  fof(f86,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_5 | ~spl2_8)),
% 0.14/0.41    inference(resolution,[],[f61,f49])).
% 0.14/0.41  fof(f61,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_8),
% 0.14/0.41    inference(avatar_component_clause,[],[f60])).
% 0.14/0.41  fof(f85,plain,(
% 0.14/0.41    spl2_13 | ~spl2_2 | ~spl2_12),
% 0.14/0.41    inference(avatar_split_clause,[],[f79,f76,f35,f82])).
% 0.14/0.41  fof(f35,plain,(
% 0.14/0.41    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.14/0.41  fof(f76,plain,(
% 0.14/0.41    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.14/0.41  fof(f79,plain,(
% 0.14/0.41    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_12)),
% 0.14/0.41    inference(resolution,[],[f77,f37])).
% 0.14/0.41  fof(f37,plain,(
% 0.14/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.14/0.41    inference(avatar_component_clause,[],[f35])).
% 0.14/0.41  fof(f77,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.14/0.41    inference(avatar_component_clause,[],[f76])).
% 0.14/0.41  fof(f78,plain,(
% 0.14/0.41    spl2_12),
% 0.14/0.41    inference(avatar_split_clause,[],[f27,f76])).
% 0.14/0.41  fof(f27,plain,(
% 0.14/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.14/0.41    inference(cnf_transformation,[],[f16])).
% 0.14/0.41  fof(f16,plain,(
% 0.14/0.41    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.14/0.41    inference(nnf_transformation,[],[f1])).
% 0.14/0.41  fof(f1,axiom,(
% 0.14/0.41    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.14/0.41  fof(f70,plain,(
% 0.14/0.41    spl2_10),
% 0.14/0.41    inference(avatar_split_clause,[],[f26,f68])).
% 0.14/0.41  fof(f26,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f13])).
% 0.14/0.41  fof(f13,plain,(
% 0.14/0.41    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.14/0.41    inference(flattening,[],[f12])).
% 0.14/0.41  fof(f12,plain,(
% 0.14/0.41    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.14/0.41    inference(ennf_transformation,[],[f4])).
% 0.14/0.41  fof(f4,axiom,(
% 0.14/0.41    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.14/0.41  fof(f66,plain,(
% 0.14/0.41    spl2_9),
% 0.14/0.41    inference(avatar_split_clause,[],[f25,f64])).
% 0.14/0.41  fof(f25,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f11])).
% 0.14/0.41  fof(f11,plain,(
% 0.14/0.41    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.14/0.41    inference(ennf_transformation,[],[f2])).
% 0.14/0.41  fof(f2,axiom,(
% 0.14/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.14/0.41  fof(f62,plain,(
% 0.14/0.41    spl2_8),
% 0.14/0.41    inference(avatar_split_clause,[],[f24,f60])).
% 0.14/0.41  fof(f24,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f10])).
% 0.14/0.41  fof(f10,plain,(
% 0.14/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.14/0.41    inference(ennf_transformation,[],[f5])).
% 0.14/0.41  fof(f5,axiom,(
% 0.14/0.41    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.14/0.41  fof(f54,plain,(
% 0.14/0.41    spl2_6),
% 0.14/0.41    inference(avatar_split_clause,[],[f23,f52])).
% 0.14/0.41  fof(f23,plain,(
% 0.14/0.41    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.14/0.41    inference(cnf_transformation,[],[f3])).
% 0.14/0.41  fof(f3,axiom,(
% 0.14/0.41    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.14/0.41  fof(f50,plain,(
% 0.14/0.41    spl2_5),
% 0.14/0.41    inference(avatar_split_clause,[],[f19,f48])).
% 0.14/0.41  fof(f19,plain,(
% 0.14/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.41    inference(cnf_transformation,[],[f6])).
% 0.14/0.41  fof(f6,axiom,(
% 0.14/0.41    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.14/0.41  fof(f38,plain,(
% 0.14/0.41    spl2_2),
% 0.14/0.41    inference(avatar_split_clause,[],[f17,f35])).
% 0.14/0.41  fof(f17,plain,(
% 0.14/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.14/0.41    inference(cnf_transformation,[],[f15])).
% 0.14/0.41  fof(f15,plain,(
% 0.14/0.41    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.14/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.14/0.41  fof(f14,plain,(
% 0.14/0.41    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.14/0.41    introduced(choice_axiom,[])).
% 0.14/0.41  fof(f9,plain,(
% 0.14/0.41    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.41    inference(ennf_transformation,[],[f8])).
% 0.14/0.41  fof(f8,negated_conjecture,(
% 0.14/0.41    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.14/0.41    inference(negated_conjecture,[],[f7])).
% 0.14/0.41  fof(f7,conjecture,(
% 0.14/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.14/0.41  fof(f33,plain,(
% 0.14/0.41    ~spl2_1),
% 0.14/0.41    inference(avatar_split_clause,[],[f18,f30])).
% 0.14/0.41  fof(f18,plain,(
% 0.14/0.41    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.14/0.41    inference(cnf_transformation,[],[f15])).
% 0.14/0.41  % SZS output end Proof for theBenchmark
% 0.14/0.41  % (28643)------------------------------
% 0.14/0.41  % (28643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.41  % (28643)Termination reason: Refutation
% 0.14/0.41  
% 0.14/0.41  % (28643)Memory used [KB]: 10618
% 0.14/0.41  % (28643)Time elapsed: 0.006 s
% 0.14/0.41  % (28643)------------------------------
% 0.14/0.41  % (28643)------------------------------
% 0.21/0.42  % (28637)Success in time 0.063 s
%------------------------------------------------------------------------------
