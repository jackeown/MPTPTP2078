%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:15 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 263 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  169 ( 637 expanded)
%              Number of equality atoms :   76 ( 300 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f196,f286])).

fof(f286,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f226,f284])).

fof(f284,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f283,f76])).

fof(f76,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f68,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f42,f36,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f283,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f98,f282])).

fof(f282,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f281,f71])).

fof(f71,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f281,plain,(
    k1_relat_1(k4_relat_1(sK2)) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(superposition,[],[f152,f163])).

fof(f163,plain,(
    k4_relat_1(sK2) = k7_relat_1(k4_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f120,f117,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f117,plain,(
    v4_relat_1(k4_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f111,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f111,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f109,f101])).

fof(f101,plain,(
    k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f109,plain,(
    m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f120,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f42,f111,f41])).

fof(f152,plain,(
    ! [X0] : k3_xboole_0(k2_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(k4_relat_1(sK2),X0)) ),
    inference(forward_demodulation,[],[f142,f71])).

fof(f142,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(k4_relat_1(sK2),X0)) = k3_xboole_0(k1_relat_1(k4_relat_1(sK2)),X0) ),
    inference(unit_resulting_resolution,[],[f120,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f98,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f226,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | spl3_2 ),
    inference(superposition,[],[f108,f165])).

fof(f165,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f36,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f108,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f62,f106])).

fof(f106,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f62,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f196,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f91,f194])).

fof(f194,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(superposition,[],[f105,f134])).

fof(f134,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f105,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f58,f103])).

% (18388)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f103,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f58,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f91,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f86,f89])).

fof(f89,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f68,f81,f46])).

fof(f81,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f36,f51])).

fof(f86,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f63,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f60,f56])).

fof(f37,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:37:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.38/0.54  % (18382)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.38/0.55  % (18390)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.38/0.55  % (18397)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.38/0.55  % (18393)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.38/0.55  % (18391)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.38/0.55  % (18376)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.38/0.56  % (18398)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.38/0.56  % (18385)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.38/0.56  % (18377)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.38/0.56  % (18389)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.38/0.56  % (18381)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.38/0.56  % (18383)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.56  % (18380)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.38/0.56  % (18379)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.38/0.56  % (18383)Refutation not found, incomplete strategy% (18383)------------------------------
% 1.38/0.56  % (18383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (18383)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (18383)Memory used [KB]: 6140
% 1.38/0.56  % (18383)Time elapsed: 0.128 s
% 1.38/0.56  % (18383)------------------------------
% 1.38/0.56  % (18383)------------------------------
% 1.38/0.56  % (18379)Refutation not found, incomplete strategy% (18379)------------------------------
% 1.38/0.56  % (18379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (18379)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (18379)Memory used [KB]: 10618
% 1.38/0.56  % (18379)Time elapsed: 0.125 s
% 1.38/0.56  % (18379)------------------------------
% 1.38/0.56  % (18379)------------------------------
% 1.38/0.56  % (18399)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.38/0.56  % (18378)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.38/0.57  % (18387)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.38/0.57  % (18399)Refutation not found, incomplete strategy% (18399)------------------------------
% 1.38/0.57  % (18399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (18395)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.38/0.57  % (18399)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (18399)Memory used [KB]: 10618
% 1.38/0.57  % (18399)Time elapsed: 0.141 s
% 1.38/0.57  % (18399)------------------------------
% 1.38/0.57  % (18399)------------------------------
% 1.38/0.57  % (18396)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.38/0.57  % (18396)Refutation not found, incomplete strategy% (18396)------------------------------
% 1.38/0.57  % (18396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (18396)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (18396)Memory used [KB]: 6140
% 1.38/0.57  % (18396)Time elapsed: 0.138 s
% 1.38/0.57  % (18396)------------------------------
% 1.38/0.57  % (18396)------------------------------
% 1.38/0.57  % (18386)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.38/0.57  % (18390)Refutation found. Thanks to Tanya!
% 1.38/0.57  % SZS status Theorem for theBenchmark
% 1.38/0.57  % SZS output start Proof for theBenchmark
% 1.38/0.57  fof(f287,plain,(
% 1.38/0.57    $false),
% 1.38/0.57    inference(avatar_sat_refutation,[],[f63,f196,f286])).
% 1.38/0.57  fof(f286,plain,(
% 1.38/0.57    spl3_2),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f285])).
% 1.38/0.57  fof(f285,plain,(
% 1.38/0.57    $false | spl3_2),
% 1.38/0.57    inference(subsumption_resolution,[],[f226,f284])).
% 1.38/0.57  fof(f284,plain,(
% 1.38/0.57    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 1.38/0.57    inference(forward_demodulation,[],[f283,f76])).
% 1.38/0.57  fof(f76,plain,(
% 1.38/0.57    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f68,f38])).
% 1.38/0.57  fof(f38,plain,(
% 1.38/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f19])).
% 1.38/0.57  fof(f19,plain,(
% 1.38/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f5])).
% 1.38/0.57  fof(f5,axiom,(
% 1.38/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.38/0.57  fof(f68,plain,(
% 1.38/0.57    v1_relat_1(sK2)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f42,f36,f41])).
% 1.38/0.57  fof(f41,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f21])).
% 1.38/0.57  fof(f21,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f1])).
% 1.38/0.57  fof(f1,axiom,(
% 1.38/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.38/0.57  fof(f36,plain,(
% 1.38/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.57    inference(cnf_transformation,[],[f35])).
% 1.38/0.57  fof(f35,plain,(
% 1.38/0.57    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).
% 1.38/0.57  fof(f34,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f18,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f17])).
% 1.38/0.57  fof(f17,negated_conjecture,(
% 1.38/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.38/0.57    inference(negated_conjecture,[],[f16])).
% 1.38/0.57  fof(f16,conjecture,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 1.38/0.57  fof(f42,plain,(
% 1.38/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f2])).
% 1.38/0.57  fof(f2,axiom,(
% 1.38/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.38/0.57  fof(f283,plain,(
% 1.38/0.57    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1)),
% 1.38/0.57    inference(superposition,[],[f98,f282])).
% 1.38/0.57  fof(f282,plain,(
% 1.38/0.57    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 1.38/0.57    inference(forward_demodulation,[],[f281,f71])).
% 1.38/0.57  fof(f71,plain,(
% 1.38/0.57    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f68,f39])).
% 1.38/0.57  fof(f39,plain,(
% 1.38/0.57    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f20])).
% 1.38/0.57  fof(f20,plain,(
% 1.38/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f7])).
% 1.38/0.57  fof(f7,axiom,(
% 1.38/0.57    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.38/0.57  fof(f281,plain,(
% 1.38/0.57    k1_relat_1(k4_relat_1(sK2)) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 1.38/0.57    inference(superposition,[],[f152,f163])).
% 1.38/0.57  fof(f163,plain,(
% 1.38/0.57    k4_relat_1(sK2) = k7_relat_1(k4_relat_1(sK2),sK1)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f120,f117,f46])).
% 1.38/0.57  fof(f46,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f26])).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(flattening,[],[f25])).
% 1.38/0.57  fof(f25,plain,(
% 1.38/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.38/0.57    inference(ennf_transformation,[],[f6])).
% 1.38/0.57  fof(f6,axiom,(
% 1.38/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.38/0.57  fof(f117,plain,(
% 1.38/0.57    v4_relat_1(k4_relat_1(sK2),sK1)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f111,f51])).
% 1.38/0.57  fof(f51,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f31])).
% 1.38/0.57  fof(f31,plain,(
% 1.38/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f9])).
% 1.38/0.57  fof(f9,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.38/0.57  fof(f111,plain,(
% 1.38/0.57    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.38/0.57    inference(forward_demodulation,[],[f109,f101])).
% 1.38/0.57  fof(f101,plain,(
% 1.38/0.57    k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f36,f47])).
% 1.38/0.57  fof(f47,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f27])).
% 1.38/0.57  fof(f27,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f13])).
% 1.38/0.57  fof(f13,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 1.38/0.57  fof(f109,plain,(
% 1.38/0.57    m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f36,f50])).
% 1.38/0.57  fof(f50,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f30])).
% 1.38/0.57  fof(f30,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f10])).
% 1.38/0.57  fof(f10,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 1.38/0.57  fof(f120,plain,(
% 1.38/0.57    v1_relat_1(k4_relat_1(sK2))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f42,f111,f41])).
% 1.38/0.57  fof(f152,plain,(
% 1.38/0.57    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(k4_relat_1(sK2),X0))) )),
% 1.38/0.57    inference(forward_demodulation,[],[f142,f71])).
% 1.38/0.57  fof(f142,plain,(
% 1.38/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(k4_relat_1(sK2),X0)) = k3_xboole_0(k1_relat_1(k4_relat_1(sK2)),X0)) )),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f120,f44])).
% 1.38/0.57  fof(f44,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f23])).
% 1.38/0.57  fof(f23,plain,(
% 1.38/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(ennf_transformation,[],[f8])).
% 1.38/0.57  fof(f8,axiom,(
% 1.38/0.57    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.38/0.57  fof(f98,plain,(
% 1.38/0.57    ( ! [X0] : (k10_relat_1(sK2,X0) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0))) )),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f68,f45])).
% 1.38/0.57  fof(f45,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f24])).
% 1.38/0.57  fof(f24,plain,(
% 1.38/0.57    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(ennf_transformation,[],[f4])).
% 1.38/0.57  fof(f4,axiom,(
% 1.38/0.57    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.38/0.57  fof(f226,plain,(
% 1.38/0.57    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | spl3_2),
% 1.38/0.57    inference(superposition,[],[f108,f165])).
% 1.38/0.57  fof(f165,plain,(
% 1.38/0.57    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f36,f54])).
% 1.38/0.57  fof(f54,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f33])).
% 1.38/0.57  fof(f33,plain,(
% 1.38/0.57    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f15])).
% 1.38/0.57  fof(f15,axiom,(
% 1.38/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.38/0.57  fof(f108,plain,(
% 1.38/0.57    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | spl3_2),
% 1.38/0.57    inference(backward_demodulation,[],[f62,f106])).
% 1.38/0.57  fof(f106,plain,(
% 1.38/0.57    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f36,f49])).
% 1.38/0.57  fof(f49,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f29])).
% 1.38/0.57  fof(f29,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f11])).
% 1.38/0.57  fof(f11,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.38/0.57  fof(f62,plain,(
% 1.38/0.57    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_2),
% 1.38/0.57    inference(avatar_component_clause,[],[f60])).
% 1.38/0.57  fof(f60,plain,(
% 1.38/0.57    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.38/0.57  fof(f196,plain,(
% 1.38/0.57    spl3_1),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f195])).
% 1.38/0.57  fof(f195,plain,(
% 1.38/0.57    $false | spl3_1),
% 1.38/0.57    inference(subsumption_resolution,[],[f91,f194])).
% 1.38/0.57  fof(f194,plain,(
% 1.38/0.57    k2_relat_1(sK2) != k9_relat_1(sK2,sK0) | spl3_1),
% 1.38/0.57    inference(superposition,[],[f105,f134])).
% 1.38/0.57  fof(f134,plain,(
% 1.38/0.57    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f36,f53])).
% 1.38/0.57  fof(f53,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f32])).
% 1.38/0.57  fof(f32,plain,(
% 1.38/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f14])).
% 1.38/0.57  fof(f14,axiom,(
% 1.38/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.38/0.57  fof(f105,plain,(
% 1.38/0.57    k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) | spl3_1),
% 1.38/0.57    inference(backward_demodulation,[],[f58,f103])).
% 1.38/0.57  % (18388)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.38/0.57  fof(f103,plain,(
% 1.38/0.57    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f36,f48])).
% 1.38/0.57  fof(f48,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f28])).
% 1.38/0.57  fof(f28,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f12])).
% 1.38/0.57  fof(f12,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.38/0.57  fof(f58,plain,(
% 1.38/0.57    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_1),
% 1.38/0.57    inference(avatar_component_clause,[],[f56])).
% 1.38/0.57  fof(f56,plain,(
% 1.38/0.57    spl3_1 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.38/0.57  fof(f91,plain,(
% 1.38/0.57    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 1.38/0.57    inference(superposition,[],[f86,f89])).
% 1.38/0.57  fof(f89,plain,(
% 1.38/0.57    sK2 = k7_relat_1(sK2,sK0)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f68,f81,f46])).
% 1.38/0.57  fof(f81,plain,(
% 1.38/0.57    v4_relat_1(sK2,sK0)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f36,f51])).
% 1.38/0.57  fof(f86,plain,(
% 1.38/0.57    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f68,f43])).
% 1.38/0.57  fof(f43,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f22])).
% 1.38/0.57  fof(f22,plain,(
% 1.38/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(ennf_transformation,[],[f3])).
% 1.38/0.57  fof(f3,axiom,(
% 1.38/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.38/0.57  fof(f63,plain,(
% 1.38/0.57    ~spl3_1 | ~spl3_2),
% 1.38/0.57    inference(avatar_split_clause,[],[f37,f60,f56])).
% 1.38/0.57  fof(f37,plain,(
% 1.38/0.57    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 1.38/0.57    inference(cnf_transformation,[],[f35])).
% 1.38/0.57  % SZS output end Proof for theBenchmark
% 1.38/0.57  % (18390)------------------------------
% 1.38/0.57  % (18390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (18390)Termination reason: Refutation
% 1.38/0.57  
% 1.38/0.57  % (18390)Memory used [KB]: 10874
% 1.38/0.57  % (18390)Time elapsed: 0.148 s
% 1.38/0.57  % (18390)------------------------------
% 1.38/0.57  % (18390)------------------------------
% 1.38/0.57  % (18386)Refutation not found, incomplete strategy% (18386)------------------------------
% 1.38/0.57  % (18386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (18386)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (18386)Memory used [KB]: 10618
% 1.38/0.57  % (18386)Time elapsed: 0.080 s
% 1.38/0.57  % (18386)------------------------------
% 1.38/0.57  % (18386)------------------------------
% 1.38/0.58  % (18394)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.38/0.58  % (18397)Refutation not found, incomplete strategy% (18397)------------------------------
% 1.38/0.58  % (18397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (18397)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (18397)Memory used [KB]: 1663
% 1.38/0.58  % (18397)Time elapsed: 0.151 s
% 1.38/0.58  % (18397)------------------------------
% 1.38/0.58  % (18397)------------------------------
% 1.38/0.58  % (18384)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.38/0.58  % (18384)Refutation not found, incomplete strategy% (18384)------------------------------
% 1.38/0.58  % (18384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (18375)Success in time 0.211 s
%------------------------------------------------------------------------------
