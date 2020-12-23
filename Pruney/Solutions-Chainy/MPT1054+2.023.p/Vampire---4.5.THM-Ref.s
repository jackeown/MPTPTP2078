%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 113 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 273 expanded)
%              Number of equality atoms :   44 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f61,f69,f77,f81,f88,f95,f99,f110,f123,f129])).

fof(f129,plain,
    ( ~ spl2_10
    | spl2_16 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl2_10
    | spl2_16 ),
    inference(unit_resulting_resolution,[],[f76,f122])).

fof(f122,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_16
  <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f76,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_10
  <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f123,plain,
    ( ~ spl2_16
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f118,f108,f97,f93,f85,f79,f59,f47,f42,f120])).

fof(f42,plain,
    ( spl2_2
  <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f59,plain,
    ( spl2_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f79,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f85,plain,
    ( spl2_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( spl2_13
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f97,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f108,plain,
    ( spl2_15
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f118,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f116,f111])).

fof(f111,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f87,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f87,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f116,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f114,f104])).

fof(f104,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f103,f60])).

% (10520)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f60,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f103,plain,
    ( ! [X0,X1] : k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f102,f94])).

fof(f94,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f102,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f100,f60])).

fof(f100,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f48,f48,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f48,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f114,plain,
    ( sK1 != k10_relat_1(k6_relat_1(sK0),sK1)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_15 ),
    inference(superposition,[],[f44,f109])).

fof(f109,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f44,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f110,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f32,f108])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f99,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f27,f97])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f95,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f28,f93])).

fof(f28,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f88,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f82,f67,f37,f85])).

fof(f37,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f67,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f82,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f39,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f81,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
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

fof(f77,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f24,f22])).

fof(f22,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f69,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f49,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f45,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f33,f42])).

fof(f33,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f20,f22])).

fof(f20,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f40,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 17:50:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.48  % (10510)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (10515)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (10508)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (10510)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f40,f45,f49,f61,f69,f77,f81,f88,f95,f99,f110,f123,f129])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~spl2_10 | spl2_16),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f124])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    $false | (~spl2_10 | spl2_16)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f76,f122])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl2_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl2_16 <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl2_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl2_10 <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ~spl2_16 | spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_11 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f118,f108,f97,f93,f85,f79,f59,f47,f42,f120])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl2_2 <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl2_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl2_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl2_12 <=> r1_tarski(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl2_13 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl2_14 <=> ! [X1,X0] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl2_15 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_11 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f117])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    sK1 != sK1 | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_11 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15)),
% 0.22/0.48    inference(forward_demodulation,[],[f116,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_11 | ~spl2_12)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f87,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | ~spl2_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f85])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    sK1 != k3_xboole_0(sK1,sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_13 | ~spl2_14 | ~spl2_15)),
% 0.22/0.48    inference(forward_demodulation,[],[f114,f104])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_6 | ~spl2_13 | ~spl2_14)),
% 0.22/0.48    inference(forward_demodulation,[],[f103,f60])).
% 0.22/0.48  % (10520)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_6 | ~spl2_13 | ~spl2_14)),
% 0.22/0.48    inference(forward_demodulation,[],[f102,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f93])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_6 | ~spl2_14)),
% 0.22/0.48    inference(forward_demodulation,[],[f100,f60])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) ) | (~spl2_3 | ~spl2_14)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f48,f48,f98])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f97])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f47])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    sK1 != k10_relat_1(k6_relat_1(sK0),sK1) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_15)),
% 0.22/0.48    inference(superposition,[],[f44,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl2_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f108])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) | spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl2_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f108])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl2_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f97])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl2_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f93])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl2_12 | ~spl2_1 | ~spl2_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f82,f67,f37,f85])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl2_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | (~spl2_1 | ~spl2_8)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f37])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl2_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f79])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl2_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f75])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f24,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl2_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f67])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f59])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f47])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f42])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.22/0.48    inference(forward_demodulation,[],[f20,f22])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f37])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (10510)------------------------------
% 0.22/0.48  % (10510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10510)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (10510)Memory used [KB]: 6140
% 0.22/0.48  % (10510)Time elapsed: 0.062 s
% 0.22/0.48  % (10510)------------------------------
% 0.22/0.48  % (10510)------------------------------
% 0.22/0.48  % (10504)Success in time 0.113 s
%------------------------------------------------------------------------------
