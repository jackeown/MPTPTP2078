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
% DateTime   : Thu Dec  3 12:57:19 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 329 expanded)
%              Number of leaves         :   26 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  331 ( 872 expanded)
%              Number of equality atoms :   81 ( 319 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f465,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f144,f179,f183,f197,f208,f264,f271,f464])).

fof(f464,plain,
    ( ~ spl3_5
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | ~ spl3_5
    | spl3_10 ),
    inference(subsumption_resolution,[],[f462,f173])).

fof(f173,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_5
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f462,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f461,f80])).

fof(f80,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f79,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).

% (21901)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f461,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_10 ),
    inference(trivial_inequality_removal,[],[f460])).

fof(f460,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_10 ),
    inference(superposition,[],[f459,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f128,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f127,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f459,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f456,f42])).

fof(f456,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_10 ),
    inference(superposition,[],[f263,f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f67,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f263,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl3_10
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f271,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f269,f115])).

fof(f115,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f269,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | spl3_9 ),
    inference(subsumption_resolution,[],[f268,f80])).

fof(f268,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK1)
    | spl3_9 ),
    inference(subsumption_resolution,[],[f266,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f266,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK1)
    | spl3_9 ),
    inference(superposition,[],[f259,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f51,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f259,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl3_9
  <=> r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f264,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_2 ),
    inference(avatar_split_clause,[],[f255,f75,f261,f257])).

fof(f75,plain,
    ( spl3_2
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f255,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f252,f80])).

fof(f252,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(superposition,[],[f250,f129])).

fof(f250,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f247,f42])).

fof(f247,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f219,f67])).

fof(f219,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f216,f42])).

fof(f216,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f77,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f77,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f208,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f206,f42])).

fof(f206,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f205])).

fof(f205,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_4 ),
    inference(superposition,[],[f143,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f143,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_4
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f197,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f195,f80])).

fof(f195,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(resolution,[],[f178,f101])).

fof(f101,plain,(
    ! [X2] :
      ( v4_relat_1(X2,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f56,f68])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f178,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl3_6
  <=> v4_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f183,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f181,f80])).

fof(f181,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f180,f116])).

fof(f116,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f180,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f174,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f174,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f179,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_3 ),
    inference(avatar_split_clause,[],[f170,f137,f176,f172])).

fof(f137,plain,
    ( spl3_3
  <=> v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f170,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f169,f80])).

fof(f169,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_3 ),
    inference(superposition,[],[f166,f129])).

fof(f166,plain,
    ( ~ v4_relat_1(sK2,k10_relat_1(sK2,sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f163,f42])).

fof(f163,plain,
    ( ~ v4_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(superposition,[],[f139,f67])).

fof(f139,plain,
    ( ~ v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f137])).

fof(f144,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f135,f71,f141,f137])).

fof(f71,plain,
    ( spl3_1
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f135,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | ~ v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f134,f80])).

fof(f134,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | spl3_1 ),
    inference(superposition,[],[f133,f122])).

fof(f133,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f132,f42])).

fof(f132,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f73,f66])).

fof(f73,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f75,f71])).

fof(f43,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.52  % (21913)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.20/0.52  % (21895)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.20/0.53  % (21896)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.20/0.53  % (21898)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.20/0.53  % (21902)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.20/0.53  % (21902)Refutation not found, incomplete strategy% (21902)------------------------------
% 1.20/0.53  % (21902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (21902)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (21902)Memory used [KB]: 10618
% 1.20/0.53  % (21902)Time elapsed: 0.108 s
% 1.20/0.53  % (21902)------------------------------
% 1.20/0.53  % (21902)------------------------------
% 1.20/0.53  % (21892)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.53  % (21895)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f465,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(avatar_sat_refutation,[],[f78,f144,f179,f183,f197,f208,f264,f271,f464])).
% 1.20/0.53  fof(f464,plain,(
% 1.20/0.53    ~spl3_5 | spl3_10),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f463])).
% 1.20/0.53  fof(f463,plain,(
% 1.20/0.53    $false | (~spl3_5 | spl3_10)),
% 1.20/0.53    inference(subsumption_resolution,[],[f462,f173])).
% 1.20/0.53  fof(f173,plain,(
% 1.20/0.53    r1_tarski(k2_relat_1(sK2),sK0) | ~spl3_5),
% 1.20/0.53    inference(avatar_component_clause,[],[f172])).
% 1.20/0.53  fof(f172,plain,(
% 1.20/0.53    spl3_5 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.20/0.53  fof(f462,plain,(
% 1.20/0.53    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_10),
% 1.20/0.53    inference(subsumption_resolution,[],[f461,f80])).
% 1.20/0.53  fof(f80,plain,(
% 1.20/0.53    v1_relat_1(sK2)),
% 1.20/0.53    inference(subsumption_resolution,[],[f79,f50])).
% 1.20/0.53  fof(f50,plain,(
% 1.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f6])).
% 1.20/0.53  fof(f6,axiom,(
% 1.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.20/0.53  fof(f79,plain,(
% 1.20/0.53    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.20/0.53    inference(resolution,[],[f49,f42])).
% 1.20/0.53  fof(f42,plain,(
% 1.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.20/0.53    inference(cnf_transformation,[],[f37])).
% 1.20/0.53  fof(f37,plain,(
% 1.20/0.53    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).
% 1.20/0.53  % (21901)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.53  fof(f36,plain,(
% 1.20/0.53    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f20,plain,(
% 1.20/0.53    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.20/0.53    inference(ennf_transformation,[],[f19])).
% 1.20/0.53  fof(f19,negated_conjecture,(
% 1.20/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.20/0.53    inference(negated_conjecture,[],[f18])).
% 1.20/0.53  fof(f18,conjecture,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 1.20/0.53  fof(f49,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f23])).
% 1.20/0.53  fof(f23,plain,(
% 1.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f2])).
% 1.20/0.53  fof(f2,axiom,(
% 1.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.20/0.53  fof(f461,plain,(
% 1.20/0.53    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_10),
% 1.20/0.53    inference(trivial_inequality_removal,[],[f460])).
% 1.20/0.53  fof(f460,plain,(
% 1.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_10),
% 1.20/0.53    inference(superposition,[],[f459,f129])).
% 1.20/0.53  fof(f129,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.20/0.53    inference(forward_demodulation,[],[f128,f45])).
% 1.20/0.53  fof(f45,plain,(
% 1.20/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f11])).
% 1.20/0.53  fof(f11,axiom,(
% 1.20/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.20/0.53  fof(f128,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f127,f44])).
% 1.20/0.53  fof(f44,plain,(
% 1.20/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f5])).
% 1.20/0.53  fof(f5,axiom,(
% 1.20/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.20/0.53  fof(f127,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.20/0.53    inference(duplicate_literal_removal,[],[f123])).
% 1.20/0.53  fof(f123,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(superposition,[],[f48,f52])).
% 1.20/0.53  fof(f52,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f26])).
% 1.20/0.53  fof(f26,plain,(
% 1.20/0.53    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(flattening,[],[f25])).
% 1.20/0.53  fof(f25,plain,(
% 1.20/0.53    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f12])).
% 1.20/0.53  fof(f12,axiom,(
% 1.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.20/0.53  fof(f48,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f22])).
% 1.20/0.53  fof(f22,plain,(
% 1.20/0.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f9])).
% 1.20/0.53  fof(f9,axiom,(
% 1.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.20/0.53  fof(f459,plain,(
% 1.20/0.53    k10_relat_1(sK2,sK0) != k1_relat_1(sK2) | spl3_10),
% 1.20/0.53    inference(subsumption_resolution,[],[f456,f42])).
% 1.20/0.53  fof(f456,plain,(
% 1.20/0.53    k10_relat_1(sK2,sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_10),
% 1.20/0.53    inference(superposition,[],[f263,f239])).
% 1.20/0.53  fof(f239,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.20/0.53    inference(duplicate_literal_removal,[],[f238])).
% 1.20/0.53  fof(f238,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.20/0.53    inference(superposition,[],[f67,f65])).
% 1.20/0.53  fof(f65,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f33])).
% 1.20/0.53  fof(f33,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.53    inference(ennf_transformation,[],[f17])).
% 1.20/0.53  fof(f17,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.20/0.53  fof(f67,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f35])).
% 1.20/0.53  fof(f35,plain,(
% 1.20/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.53    inference(ennf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.20/0.53  fof(f263,plain,(
% 1.20/0.53    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | spl3_10),
% 1.20/0.53    inference(avatar_component_clause,[],[f261])).
% 1.20/0.53  fof(f261,plain,(
% 1.20/0.53    spl3_10 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.20/0.53  fof(f271,plain,(
% 1.20/0.53    spl3_9),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f270])).
% 1.20/0.53  fof(f270,plain,(
% 1.20/0.53    $false | spl3_9),
% 1.20/0.53    inference(subsumption_resolution,[],[f269,f115])).
% 1.20/0.53  fof(f115,plain,(
% 1.20/0.53    v4_relat_1(sK2,sK1)),
% 1.20/0.53    inference(resolution,[],[f62,f42])).
% 1.20/0.53  fof(f62,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f32])).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.53    inference(ennf_transformation,[],[f13])).
% 1.20/0.53  fof(f13,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.20/0.53  fof(f269,plain,(
% 1.20/0.53    ~v4_relat_1(sK2,sK1) | spl3_9),
% 1.20/0.53    inference(subsumption_resolution,[],[f268,f80])).
% 1.20/0.53  fof(f268,plain,(
% 1.20/0.53    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK1) | spl3_9),
% 1.20/0.53    inference(subsumption_resolution,[],[f266,f68])).
% 1.20/0.53  fof(f68,plain,(
% 1.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.20/0.53    inference(equality_resolution,[],[f59])).
% 1.20/0.53  fof(f59,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.20/0.53    inference(cnf_transformation,[],[f41])).
% 1.20/0.53  fof(f41,plain,(
% 1.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.53    inference(flattening,[],[f40])).
% 1.20/0.53  fof(f40,plain,(
% 1.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.53    inference(nnf_transformation,[],[f1])).
% 1.20/0.53  fof(f1,axiom,(
% 1.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.20/0.53  fof(f266,plain,(
% 1.20/0.53    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK1) | spl3_9),
% 1.20/0.53    inference(superposition,[],[f259,f122])).
% 1.20/0.53  fof(f122,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.20/0.53    inference(duplicate_literal_removal,[],[f121])).
% 1.20/0.53  fof(f121,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(superposition,[],[f51,f57])).
% 1.20/0.53  fof(f57,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f30])).
% 1.20/0.53  fof(f30,plain,(
% 1.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(flattening,[],[f29])).
% 1.20/0.53  fof(f29,plain,(
% 1.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.20/0.53    inference(ennf_transformation,[],[f10])).
% 1.20/0.53  fof(f10,axiom,(
% 1.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.20/0.53  fof(f51,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f24,plain,(
% 1.20/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f7])).
% 1.20/0.53  fof(f7,axiom,(
% 1.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.20/0.53  fof(f259,plain,(
% 1.20/0.53    ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1)) | spl3_9),
% 1.20/0.53    inference(avatar_component_clause,[],[f257])).
% 1.20/0.53  fof(f257,plain,(
% 1.20/0.53    spl3_9 <=> r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.20/0.53  fof(f264,plain,(
% 1.20/0.53    ~spl3_9 | ~spl3_10 | spl3_2),
% 1.20/0.53    inference(avatar_split_clause,[],[f255,f75,f261,f257])).
% 1.20/0.53  fof(f75,plain,(
% 1.20/0.53    spl3_2 <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.20/0.53  fof(f255,plain,(
% 1.20/0.53    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1)) | spl3_2),
% 1.20/0.53    inference(subsumption_resolution,[],[f252,f80])).
% 1.20/0.53  fof(f252,plain,(
% 1.20/0.53    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK1)) | spl3_2),
% 1.20/0.53    inference(superposition,[],[f250,f129])).
% 1.20/0.53  fof(f250,plain,(
% 1.20/0.53    k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 1.20/0.53    inference(subsumption_resolution,[],[f247,f42])).
% 1.20/0.53  fof(f247,plain,(
% 1.20/0.53    k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 1.20/0.53    inference(superposition,[],[f219,f67])).
% 1.20/0.53  fof(f219,plain,(
% 1.20/0.53    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 1.20/0.53    inference(subsumption_resolution,[],[f216,f42])).
% 1.20/0.53  fof(f216,plain,(
% 1.20/0.53    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 1.20/0.53    inference(superposition,[],[f77,f66])).
% 1.20/0.53  fof(f66,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f34])).
% 1.20/0.53  fof(f34,plain,(
% 1.20/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.53    inference(ennf_transformation,[],[f15])).
% 1.20/0.53  fof(f15,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.20/0.53  fof(f77,plain,(
% 1.20/0.53    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | spl3_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f75])).
% 1.20/0.53  fof(f208,plain,(
% 1.20/0.53    spl3_4),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f207])).
% 1.20/0.53  fof(f207,plain,(
% 1.20/0.53    $false | spl3_4),
% 1.20/0.53    inference(subsumption_resolution,[],[f206,f42])).
% 1.20/0.53  fof(f206,plain,(
% 1.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_4),
% 1.20/0.53    inference(trivial_inequality_removal,[],[f205])).
% 1.20/0.53  fof(f205,plain,(
% 1.20/0.53    k2_relat_1(sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_4),
% 1.20/0.53    inference(superposition,[],[f143,f61])).
% 1.20/0.53  fof(f61,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f31])).
% 1.20/0.53  fof(f31,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.53    inference(ennf_transformation,[],[f14])).
% 1.20/0.53  fof(f14,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.20/0.53  fof(f143,plain,(
% 1.20/0.53    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | spl3_4),
% 1.20/0.53    inference(avatar_component_clause,[],[f141])).
% 1.20/0.53  fof(f141,plain,(
% 1.20/0.53    spl3_4 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.20/0.53  fof(f197,plain,(
% 1.20/0.53    spl3_6),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f196])).
% 1.20/0.53  fof(f196,plain,(
% 1.20/0.53    $false | spl3_6),
% 1.20/0.53    inference(subsumption_resolution,[],[f195,f80])).
% 1.20/0.53  fof(f195,plain,(
% 1.20/0.53    ~v1_relat_1(sK2) | spl3_6),
% 1.20/0.53    inference(resolution,[],[f178,f101])).
% 1.20/0.53  fof(f101,plain,(
% 1.20/0.53    ( ! [X2] : (v4_relat_1(X2,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.20/0.53    inference(resolution,[],[f56,f68])).
% 1.20/0.53  fof(f56,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f39])).
% 1.20/0.53  fof(f39,plain,(
% 1.20/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(nnf_transformation,[],[f28])).
% 1.20/0.53  fof(f28,plain,(
% 1.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f3])).
% 1.20/0.53  fof(f3,axiom,(
% 1.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.20/0.53  fof(f178,plain,(
% 1.20/0.53    ~v4_relat_1(sK2,k1_relat_1(sK2)) | spl3_6),
% 1.20/0.53    inference(avatar_component_clause,[],[f176])).
% 1.20/0.53  fof(f176,plain,(
% 1.20/0.53    spl3_6 <=> v4_relat_1(sK2,k1_relat_1(sK2))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.20/0.53  fof(f183,plain,(
% 1.20/0.53    spl3_5),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f182])).
% 1.20/0.53  fof(f182,plain,(
% 1.20/0.53    $false | spl3_5),
% 1.20/0.53    inference(subsumption_resolution,[],[f181,f80])).
% 1.20/0.53  fof(f181,plain,(
% 1.20/0.53    ~v1_relat_1(sK2) | spl3_5),
% 1.20/0.53    inference(subsumption_resolution,[],[f180,f116])).
% 1.20/0.53  fof(f116,plain,(
% 1.20/0.53    v5_relat_1(sK2,sK0)),
% 1.20/0.53    inference(resolution,[],[f63,f42])).
% 1.20/0.53  fof(f63,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f32])).
% 1.20/0.53  fof(f180,plain,(
% 1.20/0.53    ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_5),
% 1.20/0.53    inference(resolution,[],[f174,f53])).
% 1.20/0.53  fof(f53,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f38])).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(nnf_transformation,[],[f27])).
% 1.20/0.53  fof(f27,plain,(
% 1.20/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.20/0.53  fof(f174,plain,(
% 1.20/0.53    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_5),
% 1.20/0.53    inference(avatar_component_clause,[],[f172])).
% 1.20/0.53  fof(f179,plain,(
% 1.20/0.53    ~spl3_5 | ~spl3_6 | spl3_3),
% 1.20/0.53    inference(avatar_split_clause,[],[f170,f137,f176,f172])).
% 1.20/0.53  fof(f137,plain,(
% 1.20/0.53    spl3_3 <=> v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.20/0.53  fof(f170,plain,(
% 1.20/0.53    ~v4_relat_1(sK2,k1_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_3),
% 1.20/0.53    inference(subsumption_resolution,[],[f169,f80])).
% 1.20/0.53  fof(f169,plain,(
% 1.20/0.53    ~v4_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_3),
% 1.20/0.53    inference(superposition,[],[f166,f129])).
% 1.20/0.53  fof(f166,plain,(
% 1.20/0.53    ~v4_relat_1(sK2,k10_relat_1(sK2,sK0)) | spl3_3),
% 1.20/0.53    inference(subsumption_resolution,[],[f163,f42])).
% 1.20/0.53  fof(f163,plain,(
% 1.20/0.53    ~v4_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 1.20/0.53    inference(superposition,[],[f139,f67])).
% 1.20/0.53  fof(f139,plain,(
% 1.20/0.53    ~v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | spl3_3),
% 1.20/0.53    inference(avatar_component_clause,[],[f137])).
% 1.20/0.53  fof(f144,plain,(
% 1.20/0.53    ~spl3_3 | ~spl3_4 | spl3_1),
% 1.20/0.53    inference(avatar_split_clause,[],[f135,f71,f141,f137])).
% 1.20/0.53  fof(f71,plain,(
% 1.20/0.53    spl3_1 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.20/0.53  fof(f135,plain,(
% 1.20/0.53    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | ~v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | spl3_1),
% 1.20/0.53    inference(subsumption_resolution,[],[f134,f80])).
% 1.20/0.53  fof(f134,plain,(
% 1.20/0.53    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | spl3_1),
% 1.20/0.53    inference(superposition,[],[f133,f122])).
% 1.20/0.53  fof(f133,plain,(
% 1.20/0.53    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | spl3_1),
% 1.20/0.53    inference(subsumption_resolution,[],[f132,f42])).
% 1.20/0.53  fof(f132,plain,(
% 1.20/0.53    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 1.20/0.53    inference(superposition,[],[f73,f66])).
% 1.20/0.53  fof(f73,plain,(
% 1.20/0.53    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | spl3_1),
% 1.20/0.53    inference(avatar_component_clause,[],[f71])).
% 1.20/0.53  fof(f78,plain,(
% 1.20/0.53    ~spl3_1 | ~spl3_2),
% 1.20/0.53    inference(avatar_split_clause,[],[f43,f75,f71])).
% 1.20/0.53  fof(f43,plain,(
% 1.20/0.53    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 1.20/0.53    inference(cnf_transformation,[],[f37])).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (21895)------------------------------
% 1.20/0.53  % (21895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (21895)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (21895)Memory used [KB]: 6268
% 1.20/0.53  % (21895)Time elapsed: 0.116 s
% 1.20/0.53  % (21895)------------------------------
% 1.20/0.53  % (21895)------------------------------
% 1.20/0.53  % (21903)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.20/0.54  % (21911)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.20/0.54  % (21914)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.20/0.54  % (21894)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.20/0.54  % (21896)Refutation not found, incomplete strategy% (21896)------------------------------
% 1.20/0.54  % (21896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (21897)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.34/0.54  % (21905)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.34/0.54  % (21904)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (21891)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.34/0.54  % (21897)Refutation not found, incomplete strategy% (21897)------------------------------
% 1.34/0.54  % (21897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (21897)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (21897)Memory used [KB]: 10618
% 1.34/0.54  % (21897)Time elapsed: 0.089 s
% 1.34/0.54  % (21897)------------------------------
% 1.34/0.54  % (21897)------------------------------
% 1.34/0.54  % (21888)Success in time 0.175 s
%------------------------------------------------------------------------------
