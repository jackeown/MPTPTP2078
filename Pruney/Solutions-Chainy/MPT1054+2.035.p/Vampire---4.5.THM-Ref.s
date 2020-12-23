%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 112 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 ( 264 expanded)
%              Number of equality atoms :   43 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f50,f66,f74,f82,f86,f95,f99,f111,f115,f127,f133])).

fof(f133,plain,
    ( ~ spl2_11
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl2_11
    | spl2_17 ),
    inference(unit_resulting_resolution,[],[f81,f126])).

fof(f126,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl2_17
  <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f81,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_11
  <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f127,plain,
    ( ~ spl2_17
    | spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f122,f113,f108,f97,f93,f84,f64,f48,f43,f124])).

fof(f43,plain,
    ( spl2_2
  <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f48,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( spl2_7
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f84,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
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
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f113,plain,
    ( spl2_16
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f122,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f119,f120])).

fof(f120,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f110,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f110,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f119,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f117,f104])).

fof(f104,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f103,f65])).

fof(f65,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f103,plain,
    ( ! [X0,X1] : k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_7
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
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f100,f65])).

fof(f100,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f49,f49,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f49,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f117,plain,
    ( sK1 != k10_relat_1(k6_relat_1(sK0),sK1)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_16 ),
    inference(superposition,[],[f45,f114])).

fof(f114,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f113])).

fof(f45,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f115,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f33,f113])).

fof(f33,plain,(
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

fof(f111,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f87,f72,f38,f108])).

fof(f38,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f72,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f87,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f40,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f99,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f28,f97])).

fof(f28,plain,(
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

fof(f95,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f29,f93])).

fof(f29,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f86,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f30,f84])).

fof(f30,plain,(
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

fof(f82,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f25,f21])).

fof(f21,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f74,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
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

fof(f66,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f46,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f34,f43])).

fof(f34,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f20,f21])).

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

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.46  % (31950)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (31946)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (31956)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (31946)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f41,f46,f50,f66,f74,f82,f86,f95,f99,f111,f115,f127,f133])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ~spl2_11 | spl2_17),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    $false | (~spl2_11 | spl2_17)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f81,f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl2_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl2_17 <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl2_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl2_11 <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ~spl2_17 | spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15 | ~spl2_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f122,f113,f108,f97,f93,f84,f64,f48,f43,f124])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl2_2 <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl2_7 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl2_12 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl2_13 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl2_14 <=> ! [X1,X0] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl2_15 <=> r1_tarski(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl2_16 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15 | ~spl2_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f119,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_12 | ~spl2_15)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f110,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    r1_tarski(sK1,sK0) | ~spl2_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f108])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    sK1 != k3_xboole_0(sK1,sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_13 | ~spl2_14 | ~spl2_16)),
% 0.20/0.47    inference(forward_demodulation,[],[f117,f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_7 | ~spl2_13 | ~spl2_14)),
% 0.20/0.47    inference(forward_demodulation,[],[f103,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_7 | ~spl2_13 | ~spl2_14)),
% 0.20/0.47    inference(forward_demodulation,[],[f102,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_7 | ~spl2_14)),
% 0.20/0.47    inference(forward_demodulation,[],[f100,f65])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) ) | (~spl2_3 | ~spl2_14)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f49,f49,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f48])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    sK1 != k10_relat_1(k6_relat_1(sK0),sK1) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_16)),
% 0.20/0.47    inference(superposition,[],[f45,f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl2_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f113])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) | spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f43])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl2_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f113])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl2_15 | ~spl2_1 | ~spl2_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f87,f72,f38,f108])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl2_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    r1_tarski(sK1,sK0) | (~spl2_1 | ~spl2_9)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f40,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f38])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl2_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f97])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl2_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f93])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl2_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f84])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl2_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f80])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f25,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl2_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f72])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl2_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f64])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f48])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ~spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f43])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.20/0.47    inference(forward_demodulation,[],[f20,f21])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f38])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (31946)------------------------------
% 0.20/0.47  % (31946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31946)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (31946)Memory used [KB]: 6140
% 0.20/0.47  % (31946)Time elapsed: 0.053 s
% 0.20/0.47  % (31946)------------------------------
% 0.20/0.47  % (31946)------------------------------
% 0.20/0.47  % (31951)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (31945)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (31942)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (31941)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (31953)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (31952)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (31944)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (31940)Success in time 0.117 s
%------------------------------------------------------------------------------
