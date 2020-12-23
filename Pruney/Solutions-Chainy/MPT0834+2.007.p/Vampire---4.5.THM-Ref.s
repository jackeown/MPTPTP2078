%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 164 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 351 expanded)
%              Number of equality atoms :   52 ( 136 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f212,f216])).

fof(f216,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f214,f180])).

fof(f180,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f59,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f214,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | spl4_2 ),
    inference(forward_demodulation,[],[f213,f137])).

fof(f137,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f125,f136])).

fof(f136,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f134,f106])).

fof(f106,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f134,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f46,f84])).

fof(f84,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f38])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f125,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f41,f84])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f213,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | spl4_2 ),
    inference(forward_demodulation,[],[f75,f203])).

fof(f203,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f62,f38])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f75,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_2
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f212,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f210,f157])).

fof(f157,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(resolution,[],[f154,f112])).

fof(f112,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f110,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f44,f84])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f110,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | k1_relat_1(sK2) = k10_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f153,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0))
      | k1_relat_1(sK2) = k10_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f131,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f130,f84])).

fof(f130,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f42,f88])).

fof(f88,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(resolution,[],[f40,f84])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f153,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0))
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f151,f84])).

fof(f151,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0))
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f56,f88])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f210,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | spl4_1 ),
    inference(superposition,[],[f176,f208])).

fof(f208,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f63,f38])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f176,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl4_1 ),
    inference(backward_demodulation,[],[f71,f174])).

fof(f174,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f58,f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

% (3553)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f71,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_1
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f76,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f37,f73,f69])).

fof(f37,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (3569)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.47  % (3561)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (3552)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (3569)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f76,f212,f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f215])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    $false | spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f214,f180])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f59,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f18])).
% 0.21/0.49  fof(f18,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | spl4_2),
% 0.21/0.49    inference(forward_demodulation,[],[f213,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.21/0.49    inference(superposition,[],[f125,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.49    inference(resolution,[],[f134,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    v4_relat_1(sK2,sK0)),
% 0.21/0.49    inference(resolution,[],[f60,f38])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f46,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f57,f38])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f41,f84])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | spl4_2),
% 0.21/0.49    inference(forward_demodulation,[],[f75,f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f62,f38])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl4_2 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    $false | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f210,f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.21/0.49    inference(resolution,[],[f154,f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.49    inference(resolution,[],[f110,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.21/0.49    inference(resolution,[],[f44,f84])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    v5_relat_1(sK2,sK1)),
% 0.21/0.49    inference(resolution,[],[f61,f38])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | k1_relat_1(sK2) = k10_relat_1(sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f153,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) | k1_relat_1(sK2) = k10_relat_1(sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f131,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f84])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.21/0.49    inference(superposition,[],[f42,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f40,f84])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f151,f84])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.49    inference(superposition,[],[f56,f88])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | spl4_1),
% 0.21/0.49    inference(superposition,[],[f176,f208])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f63,f38])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | spl4_1),
% 0.21/0.49    inference(backward_demodulation,[],[f71,f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f58,f38])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  % (3553)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl4_1 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f73,f69])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3569)------------------------------
% 0.21/0.49  % (3569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3569)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3569)Memory used [KB]: 10746
% 0.21/0.49  % (3569)Time elapsed: 0.061 s
% 0.21/0.49  % (3569)------------------------------
% 0.21/0.49  % (3569)------------------------------
% 0.21/0.49  % (3556)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (3545)Success in time 0.144 s
%------------------------------------------------------------------------------
