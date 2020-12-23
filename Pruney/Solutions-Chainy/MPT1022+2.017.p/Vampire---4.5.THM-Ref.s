%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  153 (1129 expanded)
%              Number of leaves         :   18 ( 276 expanded)
%              Depth                    :   23
%              Number of atoms          :  452 (6513 expanded)
%              Number of equality atoms :  101 (1659 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(subsumption_resolution,[],[f317,f141])).

fof(f141,plain,(
    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f140,f128])).

fof(f128,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

% (25751)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f45,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
        | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

% (25744)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f140,plain,(
    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f139,f136])).

fof(f136,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0) ),
    inference(resolution,[],[f81,f52])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f139,plain,(
    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f138,f134])).

fof(f134,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f120,f53])).

fof(f53,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f111,f118])).

fof(f118,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f86])).

fof(f86,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f85,f52])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f117,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f116,f91])).

fof(f91,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f76,f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f116,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f115,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f115,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f114,f52])).

fof(f114,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f113,f51])).

fof(f51,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(sK2,X0,X1)
      | v2_funct_2(sK2,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f79,f49])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f110,f86])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f138,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f129,f136])).

fof(f129,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f54,f128])).

fof(f54,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f317,plain,(
    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f309,f53])).

fof(f309,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f144,f301])).

fof(f301,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f152,f300])).

fof(f300,plain,(
    sK0 = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f297,f254])).

fof(f254,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f253,f223])).

fof(f223,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f215,f85])).

fof(f215,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f214,f174])).

fof(f174,plain,(
    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f173,f50])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f173,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f172,f51])).

fof(f172,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f162,f52])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(sK2,X0,X0)
      | ~ v1_funct_2(sK2,X0,X0)
      | k2_funct_1(sK2) = k2_funct_2(X0,sK2) ) ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f214,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f213,f49])).

fof(f213,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f212,f50])).

fof(f212,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f211,f51])).

fof(f211,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f71,f52])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f253,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f252,f221])).

fof(f221,plain,(
    v5_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f215,f76])).

fof(f252,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f227,f65])).

fof(f227,plain,(
    v2_funct_2(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f216,f210])).

fof(f210,plain,(
    v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(forward_demodulation,[],[f209,f174])).

fof(f209,plain,(
    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f208,f49])).

fof(f208,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f207,f50])).

fof(f207,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f206,f51])).

fof(f206,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f216,plain,
    ( v2_funct_2(k2_funct_1(sK2),sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(resolution,[],[f215,f189])).

fof(f189,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v2_funct_2(k2_funct_1(sK2),X3)
      | ~ v3_funct_2(k2_funct_1(sK2),X2,X3) ) ),
    inference(forward_demodulation,[],[f188,f174])).

fof(f188,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v3_funct_2(k2_funct_1(sK2),X2,X3)
      | v2_funct_2(k2_funct_2(sK0,sK2),X3) ) ),
    inference(forward_demodulation,[],[f178,f174])).

fof(f178,plain,(
    ! [X2,X3] :
      ( ~ v3_funct_2(k2_funct_1(sK2),X2,X3)
      | ~ m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v2_funct_2(k2_funct_2(sK0,sK2),X3) ) ),
    inference(backward_demodulation,[],[f168,f174])).

fof(f168,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v2_funct_2(k2_funct_2(sK0,sK2),X3)
      | ~ v3_funct_2(k2_funct_2(sK0,sK2),X2,X3) ) ),
    inference(resolution,[],[f165,f79])).

fof(f165,plain,(
    v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f164,f50])).

fof(f164,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f163,f51])).

fof(f163,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK2)) ),
    inference(resolution,[],[f161,f52])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(sK2,X0,X0)
      | ~ v1_funct_2(sK2,X0,X0)
      | v1_funct_1(k2_funct_2(X0,sK2)) ) ),
    inference(resolution,[],[f68,f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f297,plain,(
    k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f242,f251])).

fof(f251,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f250,f223])).

fof(f250,plain,
    ( k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f222,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f222,plain,(
    v4_relat_1(k2_funct_1(sK2),sK0) ),
    inference(resolution,[],[f215,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f242,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) ),
    inference(resolution,[],[f223,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f152,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f151,f121])).

fof(f121,plain,(
    sK0 = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f105,f118])).

fof(f105,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f93,f104])).

fof(f104,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f103,f86])).

fof(f103,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f101,f64])).

fof(f101,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f99,f75])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f98,f86])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f49])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f93,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3) ),
    inference(resolution,[],[f61,f86])).

fof(f151,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(resolution,[],[f150,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f150,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f149,f86])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f148,f49])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f59,f109])).

fof(f109,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f108,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f107,f51])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(sK2,X0,X1)
      | v2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f78,f49])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f143,f86])).

fof(f143,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f142,f49])).

fof(f142,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f63,f109])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (25747)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (25766)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (25746)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (25750)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (25745)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (25753)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (25750)Refutation not found, incomplete strategy% (25750)------------------------------
% 0.22/0.51  % (25750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25762)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (25755)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (25758)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (25750)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25750)Memory used [KB]: 10618
% 0.22/0.51  % (25750)Time elapsed: 0.093 s
% 0.22/0.51  % (25750)------------------------------
% 0.22/0.51  % (25750)------------------------------
% 0.22/0.52  % (25747)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f319,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f317,f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.22/0.52    inference(superposition,[],[f140,f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f80,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  % (25751)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f17])).
% 0.22/0.52  fof(f17,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  % (25744)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f139,f136])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f81,f52])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f138,f134])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.22/0.52    inference(resolution,[],[f120,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.22/0.52    inference(backward_demodulation,[],[f111,f118])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    sK0 = k2_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f117,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f85,f52])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f55,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    sK0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f116,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    v5_relat_1(sK2,sK0)),
% 0.22/0.52    inference(resolution,[],[f76,f52])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f115,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    v2_funct_2(sK2,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f52])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    v2_funct_2(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.52    inference(resolution,[],[f113,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    v3_funct_2(sK2,sK0,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v3_funct_2(sK2,X0,X1) | v2_funct_2(sK2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(resolution,[],[f79,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f110,f86])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(resolution,[],[f62,f49])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f129,f136])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f54,f128])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f317,plain,(
% 0.22/0.52    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.22/0.52    inference(resolution,[],[f309,f53])).
% 0.22/0.52  fof(f309,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 0.22/0.52    inference(backward_demodulation,[],[f144,f301])).
% 0.22/0.52  fof(f301,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f152,f300])).
% 0.22/0.52  fof(f300,plain,(
% 0.22/0.52    sK0 = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f297,f254])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f253,f223])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f215,f85])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.52    inference(forward_demodulation,[],[f214,f174])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f173,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,sK0) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f172,f51])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f162,f52])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK2,X0,X0) | ~v1_funct_2(sK2,X0,X0) | k2_funct_1(sK2) = k2_funct_2(X0,sK2)) )),
% 0.22/0.52    inference(resolution,[],[f67,f49])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.52    inference(flattening,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f213,f49])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f212,f50])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f211,f51])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f71,f52])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.52    inference(flattening,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f252,f221])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    v5_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.52    inference(resolution,[],[f215,f76])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v5_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f227,f65])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    v2_funct_2(k2_funct_1(sK2),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f216,f210])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f209,f174])).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f208,f49])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f207,f50])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f206,f51])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f70,f52])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    v2_funct_2(k2_funct_1(sK2),sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 0.22/0.52    inference(resolution,[],[f215,f189])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v2_funct_2(k2_funct_1(sK2),X3) | ~v3_funct_2(k2_funct_1(sK2),X2,X3)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f188,f174])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v3_funct_2(k2_funct_1(sK2),X2,X3) | v2_funct_2(k2_funct_2(sK0,sK2),X3)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f178,f174])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~v3_funct_2(k2_funct_1(sK2),X2,X3) | ~m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v2_funct_2(k2_funct_2(sK0,sK2),X3)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f168,f174])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v2_funct_2(k2_funct_2(sK0,sK2),X3) | ~v3_funct_2(k2_funct_2(sK0,sK2),X2,X3)) )),
% 0.22/0.52    inference(resolution,[],[f165,f79])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f164,f50])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f163,f51])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK2))),
% 0.22/0.52    inference(resolution,[],[f161,f52])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK2,X0,X0) | ~v1_funct_2(sK2,X0,X0) | v1_funct_1(k2_funct_2(X0,sK2))) )),
% 0.22/0.52    inference(resolution,[],[f68,f49])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f297,plain,(
% 0.22/0.52    k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(superposition,[],[f242,f251])).
% 0.22/0.52  fof(f251,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f250,f223])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f222,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    v4_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.52    inference(resolution,[],[f215,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0))) )),
% 0.22/0.52    inference(resolution,[],[f223,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f151,f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    sK0 = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.52    inference(backward_demodulation,[],[f105,f118])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.52    inference(superposition,[],[f93,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f103,f86])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f101,f64])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.52    inference(resolution,[],[f99,f75])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f98,f86])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f58,f49])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) )),
% 0.22/0.52    inference(resolution,[],[f61,f86])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2)))),
% 0.22/0.52    inference(resolution,[],[f150,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f149,f86])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f148,f49])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(resolution,[],[f59,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f52])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.52    inference(resolution,[],[f107,f51])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v3_funct_2(sK2,X0,X1) | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(resolution,[],[f78,f49])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f86])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0] : (k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f142,f49])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0] : (k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(resolution,[],[f63,f109])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (25747)------------------------------
% 0.22/0.52  % (25747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25747)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (25747)Memory used [KB]: 6396
% 0.22/0.52  % (25747)Time elapsed: 0.096 s
% 0.22/0.52  % (25747)------------------------------
% 0.22/0.52  % (25747)------------------------------
% 0.22/0.52  % (25743)Success in time 0.158 s
%------------------------------------------------------------------------------
