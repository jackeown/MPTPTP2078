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
% DateTime   : Thu Dec  3 13:07:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 109 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  186 ( 260 expanded)
%              Number of equality atoms :   43 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f47,f59,f67,f71,f79,f88,f92,f103,f112,f120,f126])).

fof(f126,plain,
    ( ~ spl2_8
    | spl2_16 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl2_8
    | spl2_16 ),
    inference(unit_resulting_resolution,[],[f66,f119])).

fof(f119,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_16
  <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f66,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_8
  <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f120,plain,
    ( ~ spl2_16
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f115,f109,f101,f90,f86,f77,f57,f45,f40,f117])).

fof(f40,plain,
    ( spl2_2
  <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

% (9915)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f45,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( spl2_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f77,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f86,plain,
    ( spl2_12
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f90,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f101,plain,
    ( spl2_14
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f109,plain,
    ( spl2_15
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f115,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f107,f113])).

fof(f113,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f111,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f77])).

% (9916)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f111,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f107,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f105,f97])).

fof(f97,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f96,f58])).

fof(f58,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f96,plain,
    ( ! [X0,X1] : k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f95,f87])).

fof(f87,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f95,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f93,f58])).

fof(f93,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f46,f46,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f46,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f105,plain,
    ( sK1 != k10_relat_1(k6_relat_1(sK0),sK1)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_14 ),
    inference(superposition,[],[f42,f102])).

fof(f102,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f42,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f112,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f80,f69,f35,f109])).

fof(f35,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

% (9919)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% (9923)Refutation not found, incomplete strategy% (9923)------------------------------
% (9923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9923)Termination reason: Refutation not found, incomplete strategy

% (9923)Memory used [KB]: 10618
% (9923)Time elapsed: 0.071 s
% (9923)------------------------------
% (9923)------------------------------
% (9925)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f69,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f80,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f37,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f103,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f32,f101])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f92,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f27,f90])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f88,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f28,f86])).

fof(f28,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f79,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f29,f77])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f30,f69])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f22,f65])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f59,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f43,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f33,f40])).

fof(f33,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f20,f21])).

fof(f21,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f38,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:02:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (9917)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (9926)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (9918)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (9922)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (9924)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (9923)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (9914)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (9927)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (9917)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f38,f43,f47,f59,f67,f71,f79,f88,f92,f103,f112,f120,f126])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~spl2_8 | spl2_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    $false | (~spl2_8 | spl2_16)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f66,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl2_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl2_16 <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl2_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl2_8 <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ~spl2_16 | spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_11 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f115,f109,f101,f90,f86,f77,f57,f45,f40,f117])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    spl2_2 <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  % (9915)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl2_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl2_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl2_12 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl2_13 <=> ! [X1,X0] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl2_14 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl2_15 <=> r1_tarski(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_11 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f107,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_11 | ~spl2_15)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f111,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  % (9916)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0) | ~spl2_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    sK1 != k3_xboole_0(sK1,sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_12 | ~spl2_13 | ~spl2_14)),
% 0.22/0.50    inference(forward_demodulation,[],[f105,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_6 | ~spl2_12 | ~spl2_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f96,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_6 | ~spl2_12 | ~spl2_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f95,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_6 | ~spl2_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f93,f58])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) ) | (~spl2_3 | ~spl2_13)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f46,f46,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f45])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    sK1 != k10_relat_1(k6_relat_1(sK0),sK1) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_14)),
% 0.22/0.50    inference(superposition,[],[f42,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl2_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) | spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f40])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl2_15 | ~spl2_1 | ~spl2_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f80,f69,f35,f109])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  % (9919)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (9923)Refutation not found, incomplete strategy% (9923)------------------------------
% 0.22/0.50  % (9923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9923)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (9923)Memory used [KB]: 10618
% 0.22/0.50  % (9923)Time elapsed: 0.071 s
% 0.22/0.50  % (9923)------------------------------
% 0.22/0.50  % (9923)------------------------------
% 0.22/0.50  % (9925)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl2_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    r1_tarski(sK1,sK0) | (~spl2_1 | ~spl2_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f37,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f69])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f35])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl2_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f32,f101])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl2_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f90])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl2_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f86])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl2_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f29,f77])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f69])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f22,f65])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f57])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f45])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f40])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.22/0.51    inference(forward_demodulation,[],[f20,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f35])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (9917)------------------------------
% 0.22/0.51  % (9917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9917)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (9917)Memory used [KB]: 6140
% 0.22/0.51  % (9917)Time elapsed: 0.061 s
% 0.22/0.51  % (9917)------------------------------
% 0.22/0.51  % (9917)------------------------------
% 0.22/0.51  % (9911)Success in time 0.137 s
%------------------------------------------------------------------------------
