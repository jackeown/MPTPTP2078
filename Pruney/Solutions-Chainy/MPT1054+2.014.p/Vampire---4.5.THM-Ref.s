%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 140 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 268 expanded)
%              Number of equality atoms :   41 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f73,f77,f84,f97,f99,f108,f117,f128])).

fof(f128,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f127,f105,f114])).

fof(f114,plain,
    ( spl3_9
  <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f105,plain,
    ( spl3_8
  <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f125,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f30,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f125,plain,
    ( k10_relat_1(k6_partfun1(sK0),sK1) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f123,f107])).

fof(f107,plain,
    ( k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f123,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k7_relat_1(k6_partfun1(X1),X0)) ),
    inference(forward_demodulation,[],[f122,f78])).

fof(f78,plain,(
    ! [X0,X1] : k7_relat_1(k6_partfun1(X0),X1) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) ),
    inference(resolution,[],[f50,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f122,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
    inference(forward_demodulation,[],[f121,f49])).

fof(f121,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) ),
    inference(resolution,[],[f87,f47])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k6_partfun1(X1),X0)) = k10_relat_1(k6_partfun1(X1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f36,f47])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f117,plain,
    ( ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f112,f54,f114])).

fof(f54,plain,
    ( spl3_1
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f112,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl3_1 ),
    inference(superposition,[],[f56,f111])).

fof(f111,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

% (11363)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f56,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f108,plain,
    ( spl3_8
    | ~ spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f103,f90,f94,f105])).

fof(f94,plain,
    ( spl3_7
  <=> v1_relat_1(k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f90,plain,
    ( spl3_6
  <=> v4_relat_1(k6_partfun1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f103,plain,
    ( ~ v1_relat_1(k6_partfun1(sK1))
    | k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f92,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f92,plain,
    ( v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f99,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f96,f47])).

fof(f96,plain,
    ( ~ v1_relat_1(k6_partfun1(sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( spl3_6
    | ~ spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f88,f81,f94,f90])).

fof(f81,plain,
    ( spl3_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f88,plain,
    ( ~ v1_relat_1(k6_partfun1(sK1))
    | v4_relat_1(k6_partfun1(sK1),sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(X0,sK1)
        | ~ v1_relat_1(X0)
        | v4_relat_1(X0,sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f38,f83])).

fof(f83,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f84,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f79,f66,f81])).

fof(f66,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f68,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f77,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f72,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f72,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f63,f59,f70,f66])).

fof(f59,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f57,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (11355)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (11370)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (11352)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (11374)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (11377)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (11355)Refutation not found, incomplete strategy% (11355)------------------------------
% 0.22/0.54  % (11355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11355)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11355)Memory used [KB]: 6140
% 0.22/0.54  % (11355)Time elapsed: 0.128 s
% 0.22/0.54  % (11355)------------------------------
% 0.22/0.54  % (11355)------------------------------
% 0.22/0.54  % (11361)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (11377)Refutation not found, incomplete strategy% (11377)------------------------------
% 0.22/0.54  % (11377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11377)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11377)Memory used [KB]: 6268
% 0.22/0.54  % (11377)Time elapsed: 0.126 s
% 0.22/0.54  % (11377)------------------------------
% 0.22/0.54  % (11377)------------------------------
% 0.22/0.54  % (11367)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (11361)Refutation not found, incomplete strategy% (11361)------------------------------
% 0.22/0.54  % (11361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11351)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (11354)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (11372)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (11375)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (11376)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (11379)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (11380)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (11374)Refutation not found, incomplete strategy% (11374)------------------------------
% 0.22/0.55  % (11374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11353)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (11357)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (11369)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (11371)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (11364)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (11351)Refutation not found, incomplete strategy% (11351)------------------------------
% 0.22/0.55  % (11351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11367)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (11374)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11374)Memory used [KB]: 10746
% 0.22/0.55  % (11374)Time elapsed: 0.095 s
% 0.22/0.55  % (11374)------------------------------
% 0.22/0.55  % (11374)------------------------------
% 0.22/0.55  % (11366)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (11378)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (11361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11361)Memory used [KB]: 10618
% 0.22/0.55  % (11361)Time elapsed: 0.126 s
% 0.22/0.56  % (11361)------------------------------
% 0.22/0.56  % (11361)------------------------------
% 0.22/0.56  % (11353)Refutation not found, incomplete strategy% (11353)------------------------------
% 0.22/0.56  % (11353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (11360)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (11351)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (11351)Memory used [KB]: 1663
% 0.22/0.56  % (11351)Time elapsed: 0.135 s
% 0.22/0.56  % (11351)------------------------------
% 0.22/0.56  % (11351)------------------------------
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f57,f62,f73,f77,f84,f97,f99,f108,f117,f128])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    spl3_9 | ~spl3_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f127,f105,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    spl3_9 <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    spl3_8 <=> k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | ~spl3_8),
% 0.22/0.56    inference(forward_demodulation,[],[f125,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f34,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    k10_relat_1(k6_partfun1(sK0),sK1) = k1_relat_1(k6_partfun1(sK1)) | ~spl3_8),
% 0.22/0.56    inference(superposition,[],[f123,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl3_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f105])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k7_relat_1(k6_partfun1(X1),X0))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f122,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k7_relat_1(k6_partfun1(X0),X1) = k5_relat_1(k6_partfun1(X1),k6_partfun1(X0))) )),
% 0.22/0.56    inference(resolution,[],[f50,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f31,f30])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f37,f30])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f121,f49])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1)))) )),
% 0.22/0.56    inference(resolution,[],[f87,f47])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k6_partfun1(X1),X0)) = k10_relat_1(k6_partfun1(X1),k1_relat_1(X0))) )),
% 0.22/0.56    inference(resolution,[],[f36,f47])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    ~spl3_9 | spl3_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f112,f54,f114])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    spl3_1 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | spl3_1),
% 0.22/0.56    inference(superposition,[],[f56,f111])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.56    inference(resolution,[],[f45,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.56  % (11363)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl3_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f54])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    spl3_8 | ~spl3_7 | ~spl3_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f103,f90,f94,f105])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    spl3_7 <=> v1_relat_1(k6_partfun1(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    spl3_6 <=> v4_relat_1(k6_partfun1(sK1),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ~v1_relat_1(k6_partfun1(sK1)) | k6_partfun1(sK1) = k7_relat_1(k6_partfun1(sK1),sK0) | ~spl3_6),
% 0.22/0.56    inference(resolution,[],[f92,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    v4_relat_1(k6_partfun1(sK1),sK0) | ~spl3_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f90])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    spl3_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    $false | spl3_7),
% 0.22/0.56    inference(resolution,[],[f96,f47])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ~v1_relat_1(k6_partfun1(sK1)) | spl3_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f94])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    spl3_6 | ~spl3_7 | ~spl3_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f88,f81,f94,f90])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    spl3_5 <=> r1_tarski(sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ~v1_relat_1(k6_partfun1(sK1)) | v4_relat_1(k6_partfun1(sK1),sK0) | ~spl3_5),
% 0.22/0.56    inference(resolution,[],[f86,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f32,f30])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ( ! [X0] : (~v4_relat_1(X0,sK1) | ~v1_relat_1(X0) | v4_relat_1(X0,sK0)) ) | ~spl3_5),
% 0.22/0.56    inference(resolution,[],[f38,f83])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    r1_tarski(sK1,sK0) | ~spl3_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f81])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    spl3_5 | ~spl3_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f79,f66,f81])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    spl3_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.22/0.56    inference(resolution,[],[f68,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f66])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ~spl3_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    $false | ~spl3_4),
% 0.22/0.56    inference(resolution,[],[f72,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    spl3_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    spl3_3 | spl3_4 | ~spl3_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f63,f59,f70,f66])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.22/0.56    inference(resolution,[],[f39,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f59])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    spl3_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f27,f59])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.56    inference(negated_conjecture,[],[f13])).
% 0.22/0.56  fof(f13,conjecture,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ~spl3_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f28,f54])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (11367)------------------------------
% 0.22/0.56  % (11367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (11367)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (11367)Memory used [KB]: 10746
% 0.22/0.56  % (11367)Time elapsed: 0.096 s
% 0.22/0.56  % (11367)------------------------------
% 0.22/0.56  % (11367)------------------------------
% 0.22/0.56  % (11362)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (11360)Refutation not found, incomplete strategy% (11360)------------------------------
% 0.22/0.56  % (11360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (11349)Success in time 0.189 s
%------------------------------------------------------------------------------
