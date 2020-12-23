%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:38 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  117 (11386 expanded)
%              Number of leaves         :   13 (2298 expanded)
%              Depth                    :   34
%              Number of atoms          :  318 (53033 expanded)
%              Number of equality atoms :   97 (11740 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f609,plain,(
    $false ),
    inference(resolution,[],[f608,f559])).

fof(f559,plain,(
    ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f526,f550])).

fof(f550,plain,(
    ! [X0,X1] : m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(subsumption_resolution,[],[f546,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f546,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f502,f531])).

fof(f531,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f530,f37])).

fof(f530,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f520,f518])).

fof(f518,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f438,f472])).

fof(f472,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f471,f419])).

fof(f419,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f406,f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f406,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f391,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f391,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f390,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f390,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f386,f193])).

fof(f193,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f183,f37])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK4(k2_relat_1(sK3),X0))
      | r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f108,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f147,f157])).

fof(f157,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f156,f94])).

fof(f94,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f156,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f151,f35])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f147,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f66,f122,f146])).

fof(f146,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(forward_demodulation,[],[f142,f124])).

fof(f124,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f122,f49])).

fof(f142,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f56,f122])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f122,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f120,f83])).

fof(f83,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(resolution,[],[f82,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f39,f70])).

fof(f70,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f82,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f51,f35])).

% (2974)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

% (2969)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f120,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) ) ),
    inference(resolution,[],[f118,f97])).

fof(f97,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f36,f95])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f36,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X1)
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f47,f70])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f66,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f31,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f108,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK2,sK4(k2_relat_1(sK3),X2))
      | r1_tarski(k2_relat_1(sK3),X2) ) ),
    inference(resolution,[],[f105,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f105,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k2_relat_1(sK3),X1),sK2)
      | r1_tarski(k2_relat_1(sK3),X1) ) ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f103,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,k2_relat_1(sK3))
      | r2_hidden(sK4(X8,X9),sK2)
      | r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f87,f97])).

fof(f87,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK4(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f81,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f43,f44])).

fof(f386,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,X2)) ) ),
    inference(resolution,[],[f322,f46])).

fof(f322,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f321,f95])).

fof(f321,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f312,f35])).

fof(f312,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(resolution,[],[f259,f34])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(X0,X1,sK3)) ) ),
    inference(resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f471,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f425,f37])).

fof(f425,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f85,f419])).

fof(f85,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f83,f42])).

fof(f438,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f147,f419])).

fof(f520,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f98,f518])).

fof(f98,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f96,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f77,f95])).

fof(f77,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | sK2 = k2_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f42,f36])).

fof(f502,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f476,f37])).

fof(f476,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f118,f472])).

fof(f526,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(backward_demodulation,[],[f470,f518])).

fof(f470,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f422,f419])).

fof(f422,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f66,f419])).

fof(f608,plain,(
    ! [X0] : v1_funct_2(sK3,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f607,f550])).

fof(f607,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | v1_funct_2(sK3,k1_xboole_0,X0) ) ),
    inference(trivial_inequality_removal,[],[f606])).

fof(f606,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | v1_funct_2(sK3,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f62,f600])).

fof(f600,plain,(
    ! [X4,X5] : k1_xboole_0 = k1_relset_1(X4,X5,sK3) ),
    inference(forward_demodulation,[],[f592,f472])).

fof(f592,plain,(
    ! [X4,X5] : k1_relat_1(sK3) = k1_relset_1(X4,X5,sK3) ),
    inference(resolution,[],[f550,f49])).

fof(f62,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:44:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (2971)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (2970)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (2979)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (2991)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (2989)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (2983)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.67/0.59  % (2965)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.67/0.59  % (2975)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.67/0.59  % (2965)Refutation not found, incomplete strategy% (2965)------------------------------
% 1.67/0.59  % (2965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (2965)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.59  
% 1.67/0.59  % (2965)Memory used [KB]: 1663
% 1.67/0.59  % (2965)Time elapsed: 0.159 s
% 1.67/0.59  % (2965)------------------------------
% 1.67/0.59  % (2965)------------------------------
% 1.67/0.59  % (2988)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.67/0.59  % (2968)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.67/0.59  % (2975)Refutation not found, incomplete strategy% (2975)------------------------------
% 1.67/0.59  % (2975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (2975)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.59  
% 1.67/0.59  % (2975)Memory used [KB]: 10618
% 1.67/0.59  % (2975)Time elapsed: 0.170 s
% 1.67/0.59  % (2975)------------------------------
% 1.67/0.59  % (2975)------------------------------
% 1.67/0.60  % (2967)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.67/0.60  % (2973)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.67/0.60  % (2971)Refutation found. Thanks to Tanya!
% 1.67/0.60  % SZS status Theorem for theBenchmark
% 1.67/0.60  % SZS output start Proof for theBenchmark
% 1.67/0.60  fof(f609,plain,(
% 1.67/0.60    $false),
% 1.67/0.60    inference(resolution,[],[f608,f559])).
% 1.67/0.60  fof(f559,plain,(
% 1.67/0.60    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.67/0.60    inference(subsumption_resolution,[],[f526,f550])).
% 1.67/0.60  fof(f550,plain,(
% 1.67/0.60    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f546,f37])).
% 1.67/0.60  fof(f37,plain,(
% 1.67/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f3])).
% 1.67/0.60  fof(f3,axiom,(
% 1.67/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.67/0.60  fof(f546,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.60    inference(backward_demodulation,[],[f502,f531])).
% 1.67/0.60  fof(f531,plain,(
% 1.67/0.60    k1_xboole_0 = k2_relat_1(sK3)),
% 1.67/0.60    inference(subsumption_resolution,[],[f530,f37])).
% 1.67/0.60  fof(f530,plain,(
% 1.67/0.60    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.67/0.60    inference(forward_demodulation,[],[f520,f518])).
% 1.67/0.60  fof(f518,plain,(
% 1.67/0.60    k1_xboole_0 = sK2),
% 1.67/0.60    inference(subsumption_resolution,[],[f438,f472])).
% 1.67/0.60  fof(f472,plain,(
% 1.67/0.60    k1_xboole_0 = k1_relat_1(sK3)),
% 1.67/0.60    inference(forward_demodulation,[],[f471,f419])).
% 1.67/0.60  fof(f419,plain,(
% 1.67/0.60    k1_xboole_0 = sK0),
% 1.67/0.60    inference(subsumption_resolution,[],[f406,f32])).
% 1.67/0.60  fof(f32,plain,(
% 1.67/0.60    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.67/0.60    inference(cnf_transformation,[],[f17])).
% 1.67/0.60  fof(f17,plain,(
% 1.67/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.67/0.60    inference(flattening,[],[f16])).
% 1.67/0.60  fof(f16,plain,(
% 1.67/0.60    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.67/0.60    inference(ennf_transformation,[],[f14])).
% 1.67/0.60  fof(f14,negated_conjecture,(
% 1.67/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.67/0.60    inference(negated_conjecture,[],[f13])).
% 1.67/0.60  fof(f13,conjecture,(
% 1.67/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 1.67/0.60  fof(f406,plain,(
% 1.67/0.60    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.67/0.60    inference(resolution,[],[f391,f75])).
% 1.67/0.60  fof(f75,plain,(
% 1.67/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.67/0.60    inference(resolution,[],[f42,f37])).
% 1.67/0.60  fof(f42,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.67/0.60    inference(cnf_transformation,[],[f2])).
% 1.67/0.60  fof(f2,axiom,(
% 1.67/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.67/0.60  fof(f391,plain,(
% 1.67/0.60    ( ! [X0] : (r1_tarski(sK0,X0) | k1_xboole_0 = sK1) )),
% 1.67/0.60    inference(resolution,[],[f390,f44])).
% 1.67/0.60  fof(f44,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f19])).
% 1.67/0.60  fof(f19,plain,(
% 1.67/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.67/0.60    inference(ennf_transformation,[],[f1])).
% 1.67/0.60  fof(f1,axiom,(
% 1.67/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.67/0.60  fof(f390,plain,(
% 1.67/0.60    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 = sK1) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f386,f193])).
% 1.67/0.60  fof(f193,plain,(
% 1.67/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = sK1) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f183,f37])).
% 1.67/0.60  fof(f183,plain,(
% 1.67/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK4(k2_relat_1(sK3),X0)) | r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = sK1) )),
% 1.67/0.60    inference(superposition,[],[f108,f177])).
% 1.67/0.60  fof(f177,plain,(
% 1.67/0.60    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.67/0.60    inference(trivial_inequality_removal,[],[f174])).
% 1.67/0.60  fof(f174,plain,(
% 1.67/0.60    sK0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.67/0.60    inference(superposition,[],[f147,f157])).
% 1.67/0.60  fof(f157,plain,(
% 1.67/0.60    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.67/0.60    inference(superposition,[],[f156,f94])).
% 1.67/0.60  fof(f94,plain,(
% 1.67/0.60    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.67/0.60    inference(resolution,[],[f49,f35])).
% 1.67/0.60  fof(f35,plain,(
% 1.67/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.67/0.60    inference(cnf_transformation,[],[f17])).
% 1.67/0.60  fof(f49,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f24])).
% 1.67/0.60  fof(f24,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f8])).
% 1.67/0.60  fof(f8,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.67/0.60  fof(f156,plain,(
% 1.67/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.67/0.60    inference(subsumption_resolution,[],[f151,f35])).
% 1.67/0.60  fof(f151,plain,(
% 1.67/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.67/0.60    inference(resolution,[],[f57,f34])).
% 1.67/0.60  fof(f34,plain,(
% 1.67/0.60    v1_funct_2(sK3,sK0,sK1)),
% 1.67/0.60    inference(cnf_transformation,[],[f17])).
% 1.67/0.60  fof(f57,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f28])).
% 1.67/0.60  fof(f28,plain,(
% 1.67/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(flattening,[],[f27])).
% 1.67/0.60  fof(f27,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f11])).
% 1.67/0.60  fof(f11,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.67/0.60  fof(f147,plain,(
% 1.67/0.60    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.67/0.60    inference(global_subsumption,[],[f66,f122,f146])).
% 1.67/0.60  fof(f146,plain,(
% 1.67/0.60    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 1.67/0.60    inference(forward_demodulation,[],[f142,f124])).
% 1.67/0.60  fof(f124,plain,(
% 1.67/0.60    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 1.67/0.60    inference(resolution,[],[f122,f49])).
% 1.67/0.60  fof(f142,plain,(
% 1.67/0.60    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | v1_funct_2(sK3,sK0,sK2)),
% 1.67/0.60    inference(resolution,[],[f56,f122])).
% 1.67/0.60  fof(f56,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f28])).
% 1.67/0.60  fof(f122,plain,(
% 1.67/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.67/0.60    inference(resolution,[],[f120,f83])).
% 1.67/0.60  fof(f83,plain,(
% 1.67/0.60    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.67/0.60    inference(resolution,[],[f82,f74])).
% 1.67/0.60  fof(f74,plain,(
% 1.67/0.60    ( ! [X0] : (~v4_relat_1(sK3,X0) | r1_tarski(k1_relat_1(sK3),X0)) )),
% 1.67/0.60    inference(resolution,[],[f39,f70])).
% 1.67/0.60  fof(f70,plain,(
% 1.67/0.60    v1_relat_1(sK3)),
% 1.67/0.60    inference(resolution,[],[f48,f35])).
% 1.67/0.60  fof(f48,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f23])).
% 1.67/0.60  fof(f23,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f6])).
% 1.67/0.60  fof(f6,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.67/0.60  fof(f39,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f18])).
% 1.67/0.60  fof(f18,plain,(
% 1.67/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.67/0.60    inference(ennf_transformation,[],[f4])).
% 1.67/0.60  fof(f4,axiom,(
% 1.67/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.67/0.60  fof(f82,plain,(
% 1.67/0.60    v4_relat_1(sK3,sK0)),
% 1.67/0.60    inference(resolution,[],[f51,f35])).
% 1.67/0.60  % (2974)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.67/0.60  fof(f51,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f26])).
% 1.67/0.60  fof(f26,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f15])).
% 1.67/0.60  fof(f15,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.67/0.60    inference(pure_predicate_removal,[],[f7])).
% 1.67/0.60  fof(f7,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.67/0.60  % (2969)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.67/0.60  fof(f120,plain,(
% 1.67/0.60    ( ! [X1] : (~r1_tarski(k1_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))) )),
% 1.67/0.60    inference(resolution,[],[f118,f97])).
% 1.67/0.60  fof(f97,plain,(
% 1.67/0.60    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.67/0.60    inference(backward_demodulation,[],[f36,f95])).
% 1.67/0.60  fof(f95,plain,(
% 1.67/0.60    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.67/0.60    inference(resolution,[],[f50,f35])).
% 1.67/0.60  fof(f50,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f25])).
% 1.67/0.60  fof(f25,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f9])).
% 1.67/0.60  fof(f9,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.67/0.60  fof(f36,plain,(
% 1.67/0.60    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.67/0.60    inference(cnf_transformation,[],[f17])).
% 1.67/0.60  fof(f118,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),X1) | ~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.60    inference(resolution,[],[f47,f70])).
% 1.67/0.60  fof(f47,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f22])).
% 1.67/0.60  fof(f22,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.67/0.60    inference(flattening,[],[f21])).
% 1.67/0.60  fof(f21,plain,(
% 1.67/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.67/0.60    inference(ennf_transformation,[],[f10])).
% 1.67/0.60  fof(f10,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.67/0.60  fof(f66,plain,(
% 1.67/0.60    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.67/0.60    inference(subsumption_resolution,[],[f31,f33])).
% 1.67/0.60  fof(f33,plain,(
% 1.67/0.60    v1_funct_1(sK3)),
% 1.67/0.60    inference(cnf_transformation,[],[f17])).
% 1.67/0.60  fof(f31,plain,(
% 1.67/0.60    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.67/0.60    inference(cnf_transformation,[],[f17])).
% 1.67/0.60  fof(f108,plain,(
% 1.67/0.60    ( ! [X2] : (~r1_tarski(sK2,sK4(k2_relat_1(sK3),X2)) | r1_tarski(k2_relat_1(sK3),X2)) )),
% 1.67/0.60    inference(resolution,[],[f105,f46])).
% 1.67/0.60  fof(f46,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f20])).
% 1.67/0.60  fof(f20,plain,(
% 1.67/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.67/0.60    inference(ennf_transformation,[],[f5])).
% 1.67/0.60  fof(f5,axiom,(
% 1.67/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.67/0.60  fof(f105,plain,(
% 1.67/0.60    ( ! [X1] : (r2_hidden(sK4(k2_relat_1(sK3),X1),sK2) | r1_tarski(k2_relat_1(sK3),X1)) )),
% 1.67/0.60    inference(resolution,[],[f103,f59])).
% 1.67/0.60  fof(f59,plain,(
% 1.67/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.67/0.60    inference(equality_resolution,[],[f41])).
% 1.67/0.60  fof(f41,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.67/0.60    inference(cnf_transformation,[],[f2])).
% 1.67/0.60  fof(f103,plain,(
% 1.67/0.60    ( ! [X8,X9] : (~r1_tarski(X8,k2_relat_1(sK3)) | r2_hidden(sK4(X8,X9),sK2) | r1_tarski(X8,X9)) )),
% 1.67/0.60    inference(resolution,[],[f87,f97])).
% 1.67/0.60  fof(f87,plain,(
% 1.67/0.60    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK4(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 1.67/0.60    inference(resolution,[],[f81,f43])).
% 1.67/0.60  fof(f43,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f19])).
% 1.67/0.60  fof(f81,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.67/0.60    inference(resolution,[],[f43,f44])).
% 1.67/0.60  fof(f386,plain,(
% 1.67/0.60    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,X2))) )),
% 1.67/0.60    inference(resolution,[],[f322,f46])).
% 1.67/0.60  fof(f322,plain,(
% 1.67/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1) )),
% 1.67/0.60    inference(forward_demodulation,[],[f321,f95])).
% 1.67/0.60  fof(f321,plain,(
% 1.67/0.60    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f312,f35])).
% 1.67/0.60  fof(f312,plain,(
% 1.67/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))) )),
% 1.67/0.60    inference(resolution,[],[f259,f34])).
% 1.67/0.60  fof(f259,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(sK3,X2),k2_relset_1(X0,X1,sK3))) )),
% 1.67/0.60    inference(resolution,[],[f58,f33])).
% 1.67/0.60  fof(f58,plain,(
% 1.67/0.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f30])).
% 1.67/0.60  fof(f30,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.67/0.60    inference(flattening,[],[f29])).
% 1.67/0.60  fof(f29,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.67/0.60    inference(ennf_transformation,[],[f12])).
% 1.67/0.60  fof(f12,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.67/0.60  fof(f471,plain,(
% 1.67/0.60    sK0 = k1_relat_1(sK3)),
% 1.67/0.60    inference(subsumption_resolution,[],[f425,f37])).
% 1.67/0.60  fof(f425,plain,(
% 1.67/0.60    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.67/0.60    inference(backward_demodulation,[],[f85,f419])).
% 1.67/0.60  fof(f85,plain,(
% 1.67/0.60    ~r1_tarski(sK0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.67/0.60    inference(resolution,[],[f83,f42])).
% 1.67/0.60  fof(f438,plain,(
% 1.67/0.60    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.67/0.60    inference(backward_demodulation,[],[f147,f419])).
% 1.67/0.60  fof(f520,plain,(
% 1.67/0.60    k1_xboole_0 = k2_relat_1(sK3) | ~r1_tarski(sK2,k2_relat_1(sK3))),
% 1.67/0.60    inference(backward_demodulation,[],[f98,f518])).
% 1.67/0.60  fof(f98,plain,(
% 1.67/0.60    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 1.67/0.60    inference(forward_demodulation,[],[f96,f95])).
% 1.67/0.60  fof(f96,plain,(
% 1.67/0.60    sK2 = k2_relat_1(sK3) | ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 1.67/0.60    inference(backward_demodulation,[],[f77,f95])).
% 1.67/0.60  fof(f77,plain,(
% 1.67/0.60    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | sK2 = k2_relset_1(sK0,sK1,sK3)),
% 1.67/0.60    inference(resolution,[],[f42,f36])).
% 1.67/0.60  fof(f502,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f476,f37])).
% 1.67/0.60  fof(f476,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.60    inference(backward_demodulation,[],[f118,f472])).
% 1.67/0.60  fof(f526,plain,(
% 1.67/0.60    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 1.67/0.60    inference(backward_demodulation,[],[f470,f518])).
% 1.67/0.60  fof(f470,plain,(
% 1.67/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.67/0.60    inference(forward_demodulation,[],[f422,f419])).
% 1.67/0.60  fof(f422,plain,(
% 1.67/0.60    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.67/0.60    inference(backward_demodulation,[],[f66,f419])).
% 1.67/0.60  fof(f608,plain,(
% 1.67/0.60    ( ! [X0] : (v1_funct_2(sK3,k1_xboole_0,X0)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f607,f550])).
% 1.67/0.60  fof(f607,plain,(
% 1.67/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(sK3,k1_xboole_0,X0)) )),
% 1.67/0.60    inference(trivial_inequality_removal,[],[f606])).
% 1.67/0.60  fof(f606,plain,(
% 1.67/0.60    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(sK3,k1_xboole_0,X0)) )),
% 1.67/0.60    inference(superposition,[],[f62,f600])).
% 1.67/0.60  fof(f600,plain,(
% 1.67/0.60    ( ! [X4,X5] : (k1_xboole_0 = k1_relset_1(X4,X5,sK3)) )),
% 1.67/0.60    inference(forward_demodulation,[],[f592,f472])).
% 1.67/0.60  fof(f592,plain,(
% 1.67/0.60    ( ! [X4,X5] : (k1_relat_1(sK3) = k1_relset_1(X4,X5,sK3)) )),
% 1.67/0.60    inference(resolution,[],[f550,f49])).
% 1.67/0.60  fof(f62,plain,(
% 1.67/0.60    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.67/0.60    inference(equality_resolution,[],[f54])).
% 1.67/0.60  fof(f54,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f28])).
% 1.67/0.60  % SZS output end Proof for theBenchmark
% 1.67/0.60  % (2971)------------------------------
% 1.67/0.60  % (2971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (2971)Termination reason: Refutation
% 1.67/0.60  
% 1.67/0.60  % (2971)Memory used [KB]: 6396
% 1.67/0.60  % (2971)Time elapsed: 0.171 s
% 1.67/0.60  % (2971)------------------------------
% 1.67/0.60  % (2971)------------------------------
% 1.67/0.60  % (2974)Refutation not found, incomplete strategy% (2974)------------------------------
% 1.67/0.60  % (2974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (2974)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.60  
% 1.67/0.60  % (2974)Memory used [KB]: 10618
% 1.67/0.60  % (2974)Time elapsed: 0.168 s
% 1.67/0.60  % (2974)------------------------------
% 1.67/0.60  % (2974)------------------------------
% 1.67/0.60  % (2964)Success in time 0.24 s
%------------------------------------------------------------------------------
