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
% DateTime   : Thu Dec  3 13:06:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 (1629 expanded)
%              Number of leaves         :   21 ( 406 expanded)
%              Depth                    :   30
%              Number of atoms          :  507 (8992 expanded)
%              Number of equality atoms :  113 (2137 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f639,plain,(
    $false ),
    inference(subsumption_resolution,[],[f632,f64])).

fof(f64,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
      | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) )
    & r1_tarski(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
        | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) )
      & r1_tarski(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK4,sK2,sK2)
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(f632,plain,(
    ~ r1_tarski(sK3,sK2) ),
    inference(backward_demodulation,[],[f417,f620])).

fof(f620,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f212,f616])).

fof(f616,plain,(
    sK2 = k10_relat_1(sK4,sK2) ),
    inference(forward_demodulation,[],[f615,f215])).

fof(f215,plain,(
    sK2 = k9_relat_1(sK4,sK2) ),
    inference(forward_demodulation,[],[f214,f179])).

fof(f179,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f178,f141])).

fof(f141,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f132,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f132,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f63,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f178,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f177,f130])).

fof(f130,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f177,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f170,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f170,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(resolution,[],[f140,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f140,plain,(
    sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f139,f60])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f139,plain,
    ( sP1(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f128,f62])).

fof(f62,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f128,plain,
    ( sP1(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f63,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f44,f49])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f214,plain,(
    k2_relat_1(sK4) = k9_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f213,f141])).

fof(f213,plain,
    ( k2_relat_1(sK4) = k9_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f69,f157])).

fof(f157,plain,(
    sK4 = k7_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f156,f141])).

fof(f156,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f129,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f129,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f63,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f615,plain,(
    sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2)) ),
    inference(subsumption_resolution,[],[f614,f141])).

fof(f614,plain,
    ( sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f613,f60])).

fof(f613,plain,
    ( sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f609,f169])).

% (1108)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f169,plain,(
    v2_funct_1(sK4) ),
    inference(resolution,[],[f140,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f609,plain,
    ( sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f605,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f605,plain,(
    r1_tarski(sK2,k1_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f596,f430])).

fof(f430,plain,(
    sK2 = k9_relat_1(k2_funct_1(sK4),sK2) ),
    inference(forward_demodulation,[],[f429,f340])).

fof(f340,plain,(
    sK2 = k2_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f339,f305])).

fof(f305,plain,(
    v1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f296,f68])).

fof(f296,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f230,f67])).

fof(f230,plain,(
    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f227,f135])).

fof(f135,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f134,f60])).

fof(f134,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f61,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f133,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f124,f62])).

fof(f124,plain,
    ( sP0(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f63,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f227,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f81,f138])).

fof(f138,plain,(
    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) ),
    inference(subsumption_resolution,[],[f137,f60])).

fof(f137,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f136,f61])).

fof(f136,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f125,f62])).

fof(f125,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f63,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f339,plain,
    ( sK2 = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f338,f294])).

fof(f294,plain,(
    v5_relat_1(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f230,f89])).

fof(f338,plain,
    ( sK2 = k2_relat_1(k2_funct_1(sK4))
    | ~ v5_relat_1(k2_funct_1(sK4),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f331,f75])).

fof(f331,plain,(
    v2_funct_2(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f304,f92])).

fof(f304,plain,(
    sP1(sK2,k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f303,f191])).

fof(f191,plain,(
    v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f190,f60])).

fof(f190,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f189,f61])).

fof(f189,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f188,f62])).

fof(f188,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f187,f63])).

fof(f187,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f160,f77])).

fof(f160,plain,(
    v1_funct_1(k2_funct_2(sK2,sK4)) ),
    inference(resolution,[],[f135,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f303,plain,
    ( sP1(sK2,k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f292,f229])).

fof(f229,plain,(
    v3_funct_2(k2_funct_1(sK4),sK2,sK2) ),
    inference(subsumption_resolution,[],[f226,f135])).

fof(f226,plain,
    ( v3_funct_2(k2_funct_1(sK4),sK2,sK2)
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f80,f138])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f292,plain,
    ( sP1(sK2,k2_funct_1(sK4))
    | ~ v3_funct_2(k2_funct_1(sK4),sK2,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f230,f93])).

fof(f429,plain,(
    k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f428,f305])).

fof(f428,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[],[f69,f321])).

fof(f321,plain,(
    k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f320,f305])).

fof(f320,plain,
    ( k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f293,f74])).

fof(f293,plain,(
    v4_relat_1(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f230,f88])).

fof(f596,plain,(
    r1_tarski(k9_relat_1(k2_funct_1(sK4),sK2),k1_relat_1(sK4)) ),
    inference(superposition,[],[f450,f271])).

fof(f271,plain,(
    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f270,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f270,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f269,f179])).

fof(f269,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f268,f141])).

fof(f268,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f266,f60])).

fof(f266,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f72,f212])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f450,plain,(
    ! [X2] : r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2) ),
    inference(subsumption_resolution,[],[f449,f305])).

fof(f449,plain,(
    ! [X2] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2)
      | ~ v1_relat_1(k2_funct_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f435,f191])).

fof(f435,plain,(
    ! [X2] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2)
      | ~ v1_funct_1(k2_funct_1(sK4))
      | ~ v1_relat_1(k2_funct_1(sK4)) ) ),
    inference(superposition,[],[f70,f423])).

fof(f423,plain,(
    ! [X1] : k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1) ),
    inference(subsumption_resolution,[],[f422,f141])).

fof(f422,plain,(
    ! [X1] :
      ( k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f100,f169])).

fof(f100,plain,(
    ! [X1] :
      ( k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1)
      | ~ v2_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f212,plain,(
    k1_relat_1(sK4) = k10_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f207,f141])).

fof(f207,plain,
    ( k1_relat_1(sK4) = k10_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f66,f179])).

fof(f66,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f417,plain,(
    ~ r1_tarski(sK3,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f416,f141])).

fof(f416,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f415,f60])).

fof(f415,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f412,f169])).

fof(f412,plain,
    ( ~ v2_funct_1(sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( sK3 != sK3
    | ~ v2_funct_1(sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f408,f73])).

fof(f408,plain,(
    sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f407,f64])).

fof(f407,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3)) ),
    inference(forward_demodulation,[],[f406,f179])).

fof(f406,plain,
    ( sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f405,f126])).

fof(f126,plain,(
    ! [X0] : k10_relat_1(sK4,X0) = k8_relset_1(sK2,sK2,sK4,X0) ),
    inference(resolution,[],[f63,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f405,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f404,f141])).

fof(f404,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f398,f60])).

fof(f398,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( sK3 != sK3
    | sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f380,f72])).

fof(f380,plain,
    ( sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3))
    | sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3)) ),
    inference(forward_demodulation,[],[f379,f127])).

fof(f127,plain,(
    ! [X1] : k9_relat_1(sK4,X1) = k7_relset_1(sK2,sK2,sK4,X1) ),
    inference(resolution,[],[f63,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f379,plain,
    ( sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3))
    | sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(backward_demodulation,[],[f324,f127])).

fof(f324,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(backward_demodulation,[],[f65,f126])).

fof(f65,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (1114)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (1114)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (1135)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (1127)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (1111)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f639,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f632,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    r1_tarski(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    (sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f19])).
% 0.21/0.53  fof(f19,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).
% 0.21/0.53  fof(f632,plain,(
% 0.21/0.53    ~r1_tarski(sK3,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f417,f620])).
% 0.21/0.53  fof(f620,plain,(
% 0.21/0.53    sK2 = k1_relat_1(sK4)),
% 0.21/0.53    inference(backward_demodulation,[],[f212,f616])).
% 0.21/0.53  fof(f616,plain,(
% 0.21/0.53    sK2 = k10_relat_1(sK4,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f615,f215])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    sK2 = k9_relat_1(sK4,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f214,f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    sK2 = k2_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f178,f141])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.21/0.53    inference(resolution,[],[f63,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    sK2 = k2_relat_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f177,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    v5_relat_1(sK4,sK2)),
% 0.21/0.53    inference(resolution,[],[f63,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    sK2 = k2_relat_1(sK4) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f170,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    v2_funct_2(sK4,sK2)),
% 0.21/0.53    inference(resolution,[],[f140,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_funct_2(X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    sP1(sK2,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f139,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    sP1(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    v3_funct_2(sK4,sK2,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    sP1(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f63,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(definition_folding,[],[f44,f49])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    k2_relat_1(sK4) = k9_relat_1(sK4,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f213,f141])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    k2_relat_1(sK4) = k9_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f69,f157])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    sK4 = k7_relat_1(sK4,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f156,f141])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    sK4 = k7_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f129,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    v4_relat_1(sK4,sK2)),
% 0.21/0.53    inference(resolution,[],[f63,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.53  fof(f615,plain,(
% 0.21/0.53    sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f614,f141])).
% 0.21/0.53  fof(f614,plain,(
% 0.21/0.53    sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2)) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f613,f60])).
% 0.21/0.53  fof(f613,plain,(
% 0.21/0.53    sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f609,f169])).
% 0.21/0.53  % (1108)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    v2_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f140,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_funct_1(X1) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f59])).
% 0.21/0.53  fof(f609,plain,(
% 0.21/0.53    sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f605,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.53  fof(f605,plain,(
% 0.21/0.53    r1_tarski(sK2,k1_relat_1(sK4))),
% 0.21/0.53    inference(forward_demodulation,[],[f596,f430])).
% 0.21/0.53  fof(f430,plain,(
% 0.21/0.53    sK2 = k9_relat_1(k2_funct_1(sK4),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f429,f340])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    sK2 = k2_relat_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f339,f305])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    v1_relat_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f296,f68])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.21/0.53    inference(resolution,[],[f230,f67])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f227,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    sP0(sK2,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f134,f60])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    sP0(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    v1_funct_2(sK4,sK2,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    sP0(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f124,f62])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    sP0(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f63,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.53    inference(definition_folding,[],[f41,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.53    inference(flattening,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~sP0(sK2,sK4)),
% 0.21/0.53    inference(superposition,[],[f81,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f137,f60])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f136,f61])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f62])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f63,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f47])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    sK2 = k2_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f338,f294])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    v5_relat_1(k2_funct_1(sK4),sK2)),
% 0.21/0.53    inference(resolution,[],[f230,f89])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    sK2 = k2_relat_1(k2_funct_1(sK4)) | ~v5_relat_1(k2_funct_1(sK4),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(resolution,[],[f331,f75])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    v2_funct_2(k2_funct_1(sK4),sK2)),
% 0.21/0.53    inference(resolution,[],[f304,f92])).
% 0.21/0.53  fof(f304,plain,(
% 0.21/0.53    sP1(sK2,k2_funct_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f303,f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f60])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f61])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f62])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK4)) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f187,f63])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f160,f77])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_2(sK2,sK4))),
% 0.21/0.53    inference(resolution,[],[f135,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f54])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    sP1(sK2,k2_funct_1(sK4)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f292,f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    v3_funct_2(k2_funct_1(sK4),sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f226,f135])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    v3_funct_2(k2_funct_1(sK4),sK2,sK2) | ~sP0(sK2,sK4)),
% 0.21/0.53    inference(superposition,[],[f80,f138])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f54])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    sP1(sK2,k2_funct_1(sK4)) | ~v3_funct_2(k2_funct_1(sK4),sK2,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(resolution,[],[f230,f93])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f428,f305])).
% 0.21/0.53  fof(f428,plain,(
% 0.21/0.53    k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(superposition,[],[f69,f321])).
% 0.21/0.53  fof(f321,plain,(
% 0.21/0.53    k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f320,f305])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.21/0.53    inference(resolution,[],[f293,f74])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    v4_relat_1(k2_funct_1(sK4),sK2)),
% 0.21/0.53    inference(resolution,[],[f230,f88])).
% 0.21/0.53  fof(f596,plain,(
% 0.21/0.53    r1_tarski(k9_relat_1(k2_funct_1(sK4),sK2),k1_relat_1(sK4))),
% 0.21/0.53    inference(superposition,[],[f450,f271])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f270,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK2) | sK2 = k9_relat_1(sK4,k1_relat_1(sK4))),
% 0.21/0.53    inference(forward_demodulation,[],[f269,f179])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f268,f141])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f266,f60])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f72,f212])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.53  fof(f450,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f449,f305])).
% 0.21/0.53  fof(f449,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2) | ~v1_relat_1(k2_funct_1(sK4))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f435,f191])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2) | ~v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))) )),
% 0.21/0.53    inference(superposition,[],[f70,f423])).
% 0.21/0.53  fof(f423,plain,(
% 0.21/0.53    ( ! [X1] : (k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f422,f141])).
% 0.21/0.53  fof(f422,plain,(
% 0.21/0.53    ( ! [X1] : (k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1) | ~v1_relat_1(sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f169])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X1] : (k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1) | ~v2_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 0.21/0.53    inference(resolution,[],[f60,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    k1_relat_1(sK4) = k10_relat_1(sK4,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f207,f141])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    k1_relat_1(sK4) = k10_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f66,f179])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k1_relat_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f416,f141])).
% 0.21/0.53  fof(f416,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f415,f60])).
% 0.21/0.53  fof(f415,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f412,f169])).
% 0.21/0.53  fof(f412,plain,(
% 0.21/0.53    ~v2_funct_1(sK4) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f411])).
% 0.21/0.53  fof(f411,plain,(
% 0.21/0.53    sK3 != sK3 | ~v2_funct_1(sK4) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f408,f73])).
% 0.21/0.53  fof(f408,plain,(
% 0.21/0.53    sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f407,f64])).
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    ~r1_tarski(sK3,sK2) | sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3))),
% 0.21/0.53    inference(forward_demodulation,[],[f406,f179])).
% 0.21/0.53  fof(f406,plain,(
% 0.21/0.53    sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k2_relat_1(sK4))),
% 0.21/0.53    inference(forward_demodulation,[],[f405,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X0] : (k10_relat_1(sK4,X0) = k8_relset_1(sK2,sK2,sK4,X0)) )),
% 0.21/0.53    inference(resolution,[],[f63,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.53  fof(f405,plain,(
% 0.21/0.53    sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k2_relat_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f404,f141])).
% 0.21/0.53  fof(f404,plain,(
% 0.21/0.53    sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f398,f60])).
% 0.21/0.53  fof(f398,plain,(
% 0.21/0.53    sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f397])).
% 0.21/0.53  fof(f397,plain,(
% 0.21/0.53    sK3 != sK3 | sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f380,f72])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3)) | sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3))),
% 0.21/0.53    inference(forward_demodulation,[],[f379,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ( ! [X1] : (k9_relat_1(sK4,X1) = k7_relset_1(sK2,sK2,sK4,X1)) )),
% 0.21/0.53    inference(resolution,[],[f63,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3)) | sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))),
% 0.21/0.53    inference(backward_demodulation,[],[f324,f127])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))),
% 0.21/0.53    inference(backward_demodulation,[],[f65,f126])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (1114)------------------------------
% 0.21/0.53  % (1114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1114)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (1114)Memory used [KB]: 1791
% 0.21/0.53  % (1114)Time elapsed: 0.104 s
% 0.21/0.53  % (1114)------------------------------
% 0.21/0.53  % (1114)------------------------------
% 1.35/0.53  % (1104)Success in time 0.177 s
%------------------------------------------------------------------------------
