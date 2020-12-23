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
% DateTime   : Thu Dec  3 12:57:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 201 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  190 ( 479 expanded)
%              Number of equality atoms :   75 ( 222 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f197,f213])).

fof(f213,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f173,f211])).

% (18065)Refutation not found, incomplete strategy% (18065)------------------------------
% (18065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18065)Termination reason: Refutation not found, incomplete strategy

% (18065)Memory used [KB]: 6140
% (18065)Time elapsed: 0.075 s
% (18065)------------------------------
% (18065)------------------------------
fof(f211,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | spl3_2 ),
    inference(superposition,[],[f170,f206])).

fof(f206,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f38,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35])).

% (18070)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f170,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f68,f168])).

fof(f168,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f173,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f172,f78])).

fof(f78,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f70,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f172,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f133,f160])).

fof(f160,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(superposition,[],[f154,f144])).

fof(f144,plain,(
    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(forward_demodulation,[],[f141,f44])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f141,plain,(
    k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(superposition,[],[f111,f127])).

fof(f127,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f40,f122,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f122,plain,(
    v4_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f102,f41,f40,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f41,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f102,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f70,f100,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f100,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f111,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f154,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f153,f44])).

fof(f153,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f152,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f152,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f145,f44])).

fof(f145,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f40,f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f133,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f197,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f120,f195])).

fof(f195,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(superposition,[],[f176,f187])).

fof(f187,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f38,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f176,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f64,f174])).

fof(f174,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f38,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
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

fof(f64,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_1
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f120,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f112,f117])).

fof(f117,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f70,f98,f53])).

fof(f98,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f70,f48])).

fof(f69,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f66,f62])).

fof(f39,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:27:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (18060)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  % (18062)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.54  % (18078)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.54  % (18079)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.54  % (18063)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.54  % (18064)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.54  % (18074)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.54  % (18077)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.54  % (18059)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.54  % (18072)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (18061)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.55  % (18072)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (18058)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.55  % (18061)Refutation not found, incomplete strategy% (18061)------------------------------
% 0.22/0.55  % (18061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18061)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18061)Memory used [KB]: 10618
% 0.22/0.55  % (18061)Time elapsed: 0.118 s
% 0.22/0.55  % (18061)------------------------------
% 0.22/0.55  % (18061)------------------------------
% 0.22/0.56  % (18081)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.56  % (18073)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.56  % (18078)Refutation not found, incomplete strategy% (18078)------------------------------
% 0.22/0.56  % (18078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18078)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18078)Memory used [KB]: 6140
% 0.22/0.56  % (18078)Time elapsed: 0.135 s
% 0.22/0.56  % (18078)------------------------------
% 0.22/0.56  % (18078)------------------------------
% 0.22/0.56  % (18076)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.56  % (18074)Refutation not found, incomplete strategy% (18074)------------------------------
% 0.22/0.56  % (18074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18074)Memory used [KB]: 1663
% 0.22/0.56  % (18074)Time elapsed: 0.133 s
% 0.22/0.56  % (18074)------------------------------
% 0.22/0.56  % (18074)------------------------------
% 0.22/0.56  % (18069)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.56  % (18065)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (18075)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.56  % (18064)Refutation not found, incomplete strategy% (18064)------------------------------
% 0.22/0.56  % (18064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18064)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18064)Memory used [KB]: 10618
% 0.22/0.56  % (18064)Time elapsed: 0.133 s
% 0.22/0.56  % (18064)------------------------------
% 0.22/0.56  % (18064)------------------------------
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f69,f197,f213])).
% 0.22/0.56  fof(f213,plain,(
% 0.22/0.56    spl3_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f212])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    $false | spl3_2),
% 0.22/0.56    inference(subsumption_resolution,[],[f173,f211])).
% 0.22/0.56  % (18065)Refutation not found, incomplete strategy% (18065)------------------------------
% 0.22/0.56  % (18065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18065)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18065)Memory used [KB]: 6140
% 0.22/0.56  % (18065)Time elapsed: 0.075 s
% 0.22/0.56  % (18065)------------------------------
% 0.22/0.56  % (18065)------------------------------
% 0.22/0.56  fof(f211,plain,(
% 0.22/0.56    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | spl3_2),
% 0.22/0.56    inference(superposition,[],[f170,f206])).
% 0.22/0.56  fof(f206,plain,(
% 0.22/0.56    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f38,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35])).
% 0.22/0.56  % (18070)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.56    inference(negated_conjecture,[],[f17])).
% 0.22/0.56  fof(f17,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | spl3_2),
% 0.22/0.56    inference(backward_demodulation,[],[f68,f168])).
% 0.22/0.56  fof(f168,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f38,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f172,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f70,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    v1_relat_1(sK2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f38,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1)),
% 0.22/0.56    inference(superposition,[],[f133,f160])).
% 0.22/0.56  fof(f160,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.22/0.56    inference(superposition,[],[f154,f144])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f141,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.22/0.56    inference(superposition,[],[f111,f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f40,f122,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    v4_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f102,f41,f40,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f70,f100,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    v5_relat_1(sK2,sK1)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f38,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f40,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f153,f44])).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f152,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.56  fof(f152,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f145,f44])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f40,f40,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    ( ! [X0] : (k10_relat_1(sK2,X0) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0))) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f70,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.56  fof(f197,plain,(
% 0.22/0.56    spl3_1),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f196])).
% 0.22/0.56  fof(f196,plain,(
% 0.22/0.56    $false | spl3_1),
% 0.22/0.56    inference(subsumption_resolution,[],[f120,f195])).
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    k2_relat_1(sK2) != k9_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.56    inference(superposition,[],[f176,f187])).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f38,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.56  fof(f176,plain,(
% 0.22/0.56    k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) | spl3_1),
% 0.22/0.56    inference(backward_demodulation,[],[f64,f174])).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f38,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    spl3_1 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.22/0.56    inference(superposition,[],[f112,f117])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    sK2 = k7_relat_1(sK2,sK0)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f70,f98,f53])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    v4_relat_1(sK2,sK0)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f38,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f70,f48])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ~spl3_1 | ~spl3_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f39,f66,f62])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (18072)------------------------------
% 0.22/0.56  % (18072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18072)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (18072)Memory used [KB]: 10746
% 0.22/0.56  % (18072)Time elapsed: 0.115 s
% 0.22/0.56  % (18072)------------------------------
% 0.22/0.56  % (18072)------------------------------
% 0.22/0.56  % (18066)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.57  % (18057)Success in time 0.202 s
%------------------------------------------------------------------------------
