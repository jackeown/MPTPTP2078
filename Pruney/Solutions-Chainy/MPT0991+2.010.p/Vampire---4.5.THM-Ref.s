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
% DateTime   : Thu Dec  3 13:03:05 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 136 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  242 ( 755 expanded)
%              Number of equality atoms :   35 (  93 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (29722)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f315,f37])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f315,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f285,f59])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f285,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f121,f275])).

fof(f275,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f273,f56])).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f41,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f273,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f138,f260])).

fof(f260,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f256,f123])).

fof(f123,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f122,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f122,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f31,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f31,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

fof(f256,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f252,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f171,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f171,plain,(
    ! [X17,X15,X18,X16] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | m1_subset_1(k1_partfun1(X15,X16,X17,X18,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X15,X18))) ) ),
    inference(resolution,[],[f69,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X24,X23,X21,X22,X20] :
      ( ~ v1_funct_1(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(k1_partfun1(X21,X22,X23,X24,X20,sK3),k1_zfmisc_1(k2_zfmisc_1(X21,X24))) ) ),
    inference(resolution,[],[f28,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f138,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f137,f30])).

fof(f137,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f136,f28])).

fof(f136,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f100,f29])).

fof(f29,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X2,sK1,X3)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | k1_xboole_0 = X3 ) ),
    inference(subsumption_resolution,[],[f99,f36])).

fof(f36,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | k1_xboole_0 = X3
      | v2_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f98,f34])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | k1_xboole_0 = X3
      | v2_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f94,f32])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | k1_xboole_0 = X3
      | v2_funct_1(sK2) ) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f33,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f120,f85])).

fof(f85,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f84,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f83,f32])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f120,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 18:17:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1223458817)
% 0.14/0.37  ipcrm: permission denied for id (1223557124)
% 0.14/0.38  ipcrm: permission denied for id (1223622662)
% 0.14/0.38  ipcrm: permission denied for id (1227915272)
% 0.14/0.38  ipcrm: permission denied for id (1223720969)
% 0.14/0.38  ipcrm: permission denied for id (1223753738)
% 0.14/0.38  ipcrm: permission denied for id (1223786507)
% 0.14/0.38  ipcrm: permission denied for id (1223819276)
% 0.14/0.38  ipcrm: permission denied for id (1227948045)
% 0.14/0.39  ipcrm: permission denied for id (1223917583)
% 0.14/0.39  ipcrm: permission denied for id (1228046353)
% 0.14/0.39  ipcrm: permission denied for id (1224015890)
% 0.14/0.39  ipcrm: permission denied for id (1224048659)
% 0.14/0.39  ipcrm: permission denied for id (1228079124)
% 0.14/0.40  ipcrm: permission denied for id (1224114197)
% 0.14/0.40  ipcrm: permission denied for id (1224146966)
% 0.14/0.40  ipcrm: permission denied for id (1228144664)
% 0.14/0.40  ipcrm: permission denied for id (1224278041)
% 0.20/0.40  ipcrm: permission denied for id (1224310810)
% 0.20/0.40  ipcrm: permission denied for id (1224343579)
% 0.20/0.40  ipcrm: permission denied for id (1224376348)
% 0.20/0.41  ipcrm: permission denied for id (1228242974)
% 0.20/0.41  ipcrm: permission denied for id (1224507424)
% 0.20/0.41  ipcrm: permission denied for id (1228308513)
% 0.20/0.41  ipcrm: permission denied for id (1224572962)
% 0.20/0.41  ipcrm: permission denied for id (1224605731)
% 0.20/0.41  ipcrm: permission denied for id (1224638500)
% 0.20/0.42  ipcrm: permission denied for id (1224671269)
% 0.20/0.42  ipcrm: permission denied for id (1224704038)
% 0.20/0.42  ipcrm: permission denied for id (1224769576)
% 0.20/0.42  ipcrm: permission denied for id (1228406825)
% 0.20/0.42  ipcrm: permission denied for id (1228439594)
% 0.20/0.42  ipcrm: permission denied for id (1228505132)
% 0.20/0.43  ipcrm: permission denied for id (1228537901)
% 0.20/0.43  ipcrm: permission denied for id (1224966190)
% 0.20/0.43  ipcrm: permission denied for id (1224998959)
% 0.20/0.43  ipcrm: permission denied for id (1228636209)
% 0.20/0.43  ipcrm: permission denied for id (1225130035)
% 0.20/0.44  ipcrm: permission denied for id (1228701748)
% 0.20/0.44  ipcrm: permission denied for id (1228734517)
% 0.20/0.44  ipcrm: permission denied for id (1225228342)
% 0.20/0.44  ipcrm: permission denied for id (1225261111)
% 0.20/0.44  ipcrm: permission denied for id (1228767288)
% 0.20/0.44  ipcrm: permission denied for id (1225326649)
% 0.20/0.44  ipcrm: permission denied for id (1225359418)
% 0.20/0.45  ipcrm: permission denied for id (1225424956)
% 0.20/0.45  ipcrm: permission denied for id (1228832829)
% 0.20/0.45  ipcrm: permission denied for id (1225490494)
% 0.20/0.45  ipcrm: permission denied for id (1228865599)
% 0.20/0.45  ipcrm: permission denied for id (1228898368)
% 0.20/0.45  ipcrm: permission denied for id (1225588801)
% 0.20/0.45  ipcrm: permission denied for id (1228931138)
% 0.20/0.46  ipcrm: permission denied for id (1228963907)
% 0.20/0.46  ipcrm: permission denied for id (1225752645)
% 0.20/0.46  ipcrm: permission denied for id (1225785414)
% 0.20/0.46  ipcrm: permission denied for id (1225818183)
% 0.20/0.46  ipcrm: permission denied for id (1225850952)
% 0.20/0.46  ipcrm: permission denied for id (1225883721)
% 0.20/0.46  ipcrm: permission denied for id (1229029450)
% 0.20/0.47  ipcrm: permission denied for id (1229062219)
% 0.20/0.47  ipcrm: permission denied for id (1229127757)
% 0.20/0.47  ipcrm: permission denied for id (1226113103)
% 0.20/0.47  ipcrm: permission denied for id (1226178641)
% 0.20/0.48  ipcrm: permission denied for id (1226244179)
% 0.20/0.48  ipcrm: permission denied for id (1226309717)
% 0.20/0.48  ipcrm: permission denied for id (1226342486)
% 0.20/0.48  ipcrm: permission denied for id (1226375255)
% 0.20/0.48  ipcrm: permission denied for id (1226408024)
% 0.20/0.48  ipcrm: permission denied for id (1229291609)
% 0.20/0.49  ipcrm: permission denied for id (1226506331)
% 0.20/0.49  ipcrm: permission denied for id (1226539100)
% 0.20/0.49  ipcrm: permission denied for id (1226571869)
% 0.20/0.49  ipcrm: permission denied for id (1226604638)
% 0.20/0.49  ipcrm: permission denied for id (1226637407)
% 0.20/0.49  ipcrm: permission denied for id (1226702945)
% 0.20/0.50  ipcrm: permission denied for id (1226735714)
% 0.20/0.50  ipcrm: permission denied for id (1226768483)
% 0.20/0.50  ipcrm: permission denied for id (1226899558)
% 0.20/0.50  ipcrm: permission denied for id (1226997863)
% 0.20/0.50  ipcrm: permission denied for id (1229455464)
% 0.20/0.51  ipcrm: permission denied for id (1229521002)
% 0.20/0.51  ipcrm: permission denied for id (1229619307)
% 0.20/0.51  ipcrm: permission denied for id (1229652077)
% 0.20/0.51  ipcrm: permission denied for id (1227194478)
% 0.20/0.51  ipcrm: permission denied for id (1227227247)
% 0.20/0.51  ipcrm: permission denied for id (1227260016)
% 0.20/0.52  ipcrm: permission denied for id (1229717618)
% 0.20/0.52  ipcrm: permission denied for id (1227456630)
% 0.20/0.52  ipcrm: permission denied for id (1227489399)
% 0.20/0.52  ipcrm: permission denied for id (1229881465)
% 0.20/0.53  ipcrm: permission denied for id (1227587706)
% 0.20/0.53  ipcrm: permission denied for id (1229947004)
% 0.20/0.53  ipcrm: permission denied for id (1229979773)
% 0.20/0.53  ipcrm: permission denied for id (1230012542)
% 1.10/0.68  % (29720)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.10/0.68  % (29702)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.10/0.68  % (29706)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.10/0.68  % (29703)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.10/0.68  % (29729)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.10/0.69  % (29719)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.10/0.69  % (29713)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.10/0.69  % (29709)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.10/0.69  % (29711)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.10/0.69  % (29716)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.10/0.69  % (29713)Refutation not found, incomplete strategy% (29713)------------------------------
% 1.10/0.69  % (29713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.69  % (29707)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.10/0.69  % (29715)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.10/0.70  % (29712)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.10/0.70  % (29720)Refutation found. Thanks to Tanya!
% 1.10/0.70  % SZS status Theorem for theBenchmark
% 1.10/0.70  % (29719)Refutation not found, incomplete strategy% (29719)------------------------------
% 1.10/0.70  % (29719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.70  % (29713)Termination reason: Refutation not found, incomplete strategy
% 1.10/0.70  
% 1.10/0.70  % (29713)Memory used [KB]: 10746
% 1.10/0.70  % (29713)Time elapsed: 0.110 s
% 1.10/0.70  % (29713)------------------------------
% 1.10/0.70  % (29713)------------------------------
% 1.10/0.70  % (29721)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.10/0.70  % (29705)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.10/0.70  % (29719)Termination reason: Refutation not found, incomplete strategy
% 1.10/0.70  
% 1.10/0.70  % (29719)Memory used [KB]: 10746
% 1.10/0.70  % (29719)Time elapsed: 0.115 s
% 1.10/0.70  % (29719)------------------------------
% 1.10/0.70  % (29719)------------------------------
% 1.44/0.70  % (29733)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.71  % SZS output start Proof for theBenchmark
% 1.44/0.71  % (29722)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.71  fof(f316,plain,(
% 1.44/0.71    $false),
% 1.44/0.71    inference(subsumption_resolution,[],[f315,f37])).
% 1.44/0.71  fof(f37,plain,(
% 1.44/0.71    v1_xboole_0(k1_xboole_0)),
% 1.44/0.71    inference(cnf_transformation,[],[f1])).
% 1.44/0.71  fof(f1,axiom,(
% 1.44/0.71    v1_xboole_0(k1_xboole_0)),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.44/0.71  fof(f315,plain,(
% 1.44/0.71    ~v1_xboole_0(k1_xboole_0)),
% 1.44/0.71    inference(forward_demodulation,[],[f285,f59])).
% 1.44/0.71  fof(f59,plain,(
% 1.44/0.71    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.44/0.71    inference(equality_resolution,[],[f47])).
% 1.44/0.71  fof(f47,plain,(
% 1.44/0.71    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.44/0.71    inference(cnf_transformation,[],[f2])).
% 1.44/0.71  fof(f2,axiom,(
% 1.44/0.71    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.44/0.71  fof(f285,plain,(
% 1.44/0.71    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))),
% 1.44/0.71    inference(backward_demodulation,[],[f121,f275])).
% 1.44/0.71  fof(f275,plain,(
% 1.44/0.71    k1_xboole_0 = sK0),
% 1.44/0.71    inference(subsumption_resolution,[],[f273,f56])).
% 1.44/0.71  fof(f56,plain,(
% 1.44/0.71    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.44/0.71    inference(definition_unfolding,[],[f41,f38])).
% 1.44/0.71  fof(f38,plain,(
% 1.44/0.71    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.44/0.71    inference(cnf_transformation,[],[f11])).
% 1.44/0.71  fof(f11,axiom,(
% 1.44/0.71    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.44/0.71  fof(f41,plain,(
% 1.44/0.71    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.44/0.71    inference(cnf_transformation,[],[f7])).
% 1.44/0.71  fof(f7,axiom,(
% 1.44/0.71    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.44/0.71  fof(f273,plain,(
% 1.44/0.71    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0),
% 1.44/0.71    inference(backward_demodulation,[],[f138,f260])).
% 1.44/0.71  fof(f260,plain,(
% 1.44/0.71    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.44/0.71    inference(resolution,[],[f256,f123])).
% 1.44/0.71  fof(f123,plain,(
% 1.44/0.71    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.44/0.71    inference(subsumption_resolution,[],[f122,f55])).
% 1.44/0.71  fof(f55,plain,(
% 1.44/0.71    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.44/0.71    inference(definition_unfolding,[],[f39,f38])).
% 1.44/0.71  fof(f39,plain,(
% 1.44/0.71    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.44/0.71    inference(cnf_transformation,[],[f9])).
% 1.44/0.71  fof(f9,axiom,(
% 1.44/0.71    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.44/0.71  fof(f122,plain,(
% 1.44/0.71    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.44/0.71    inference(resolution,[],[f31,f52])).
% 1.44/0.71  fof(f52,plain,(
% 1.44/0.71    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.44/0.71    inference(cnf_transformation,[],[f25])).
% 1.44/0.71  fof(f25,plain,(
% 1.44/0.71    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.71    inference(flattening,[],[f24])).
% 1.44/0.71  fof(f24,plain,(
% 1.44/0.71    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.44/0.71    inference(ennf_transformation,[],[f8])).
% 1.44/0.71  fof(f8,axiom,(
% 1.44/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.44/0.71  fof(f31,plain,(
% 1.44/0.71    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f16,plain,(
% 1.44/0.71    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.44/0.71    inference(flattening,[],[f15])).
% 1.44/0.71  fof(f15,plain,(
% 1.44/0.71    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.44/0.71    inference(ennf_transformation,[],[f14])).
% 1.44/0.71  fof(f14,negated_conjecture,(
% 1.44/0.71    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 1.44/0.71    inference(negated_conjecture,[],[f13])).
% 1.44/0.71  fof(f13,conjecture,(
% 1.44/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).
% 1.44/0.71  fof(f256,plain,(
% 1.44/0.71    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.71    inference(resolution,[],[f252,f30])).
% 1.44/0.71  fof(f30,plain,(
% 1.44/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f252,plain,(
% 1.44/0.71    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 1.44/0.71    inference(resolution,[],[f171,f34])).
% 1.44/0.71  fof(f34,plain,(
% 1.44/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f171,plain,(
% 1.44/0.71    ( ! [X17,X15,X18,X16] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) | m1_subset_1(k1_partfun1(X15,X16,X17,X18,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X15,X18)))) )),
% 1.44/0.71    inference(resolution,[],[f69,f32])).
% 1.44/0.71  fof(f32,plain,(
% 1.44/0.71    v1_funct_1(sK2)),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f69,plain,(
% 1.44/0.71    ( ! [X24,X23,X21,X22,X20] : (~v1_funct_1(X20) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | m1_subset_1(k1_partfun1(X21,X22,X23,X24,X20,sK3),k1_zfmisc_1(k2_zfmisc_1(X21,X24)))) )),
% 1.44/0.71    inference(resolution,[],[f28,f54])).
% 1.44/0.71  fof(f54,plain,(
% 1.44/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.44/0.71    inference(cnf_transformation,[],[f27])).
% 1.44/0.71  fof(f27,plain,(
% 1.44/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.44/0.71    inference(flattening,[],[f26])).
% 1.44/0.71  fof(f26,plain,(
% 1.44/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.44/0.71    inference(ennf_transformation,[],[f10])).
% 1.44/0.71  fof(f10,axiom,(
% 1.44/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.44/0.71  fof(f28,plain,(
% 1.44/0.71    v1_funct_1(sK3)),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f138,plain,(
% 1.44/0.71    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0),
% 1.44/0.71    inference(subsumption_resolution,[],[f137,f30])).
% 1.44/0.71  fof(f137,plain,(
% 1.44/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0),
% 1.44/0.71    inference(subsumption_resolution,[],[f136,f28])).
% 1.44/0.71  fof(f136,plain,(
% 1.44/0.71    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0),
% 1.44/0.71    inference(resolution,[],[f100,f29])).
% 1.44/0.71  fof(f29,plain,(
% 1.44/0.71    v1_funct_2(sK3,sK1,sK0)),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f100,plain,(
% 1.44/0.71    ( ! [X2,X3] : (~v1_funct_2(X2,sK1,X3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | k1_xboole_0 = X3) )),
% 1.44/0.71    inference(subsumption_resolution,[],[f99,f36])).
% 1.44/0.71  fof(f36,plain,(
% 1.44/0.71    ~v2_funct_1(sK2)),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f99,plain,(
% 1.44/0.71    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_funct_2(X2,sK1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | k1_xboole_0 = X3 | v2_funct_1(sK2)) )),
% 1.44/0.71    inference(subsumption_resolution,[],[f98,f34])).
% 1.44/0.71  fof(f98,plain,(
% 1.44/0.71    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | k1_xboole_0 = X3 | v2_funct_1(sK2)) )),
% 1.44/0.71    inference(subsumption_resolution,[],[f94,f32])).
% 1.44/0.71  fof(f94,plain,(
% 1.44/0.71    ( ! [X2,X3] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | k1_xboole_0 = X3 | v2_funct_1(sK2)) )),
% 1.44/0.71    inference(resolution,[],[f33,f49])).
% 1.44/0.71  fof(f49,plain,(
% 1.44/0.71    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 1.44/0.71    inference(cnf_transformation,[],[f23])).
% 1.44/0.71  fof(f23,plain,(
% 1.44/0.71    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.44/0.71    inference(flattening,[],[f22])).
% 1.44/0.71  fof(f22,plain,(
% 1.44/0.71    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.44/0.71    inference(ennf_transformation,[],[f12])).
% 1.44/0.71  fof(f12,axiom,(
% 1.44/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.44/0.71  fof(f33,plain,(
% 1.44/0.71    v1_funct_2(sK2,sK0,sK1)),
% 1.44/0.71    inference(cnf_transformation,[],[f16])).
% 1.44/0.71  fof(f121,plain,(
% 1.44/0.71    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.44/0.71    inference(subsumption_resolution,[],[f120,f85])).
% 1.44/0.71  fof(f85,plain,(
% 1.44/0.71    ~v1_xboole_0(sK2)),
% 1.44/0.71    inference(subsumption_resolution,[],[f84,f42])).
% 1.44/0.71  fof(f42,plain,(
% 1.44/0.71    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.44/0.71    inference(cnf_transformation,[],[f17])).
% 1.44/0.71  fof(f17,plain,(
% 1.44/0.71    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.44/0.71    inference(ennf_transformation,[],[f4])).
% 1.44/0.71  fof(f4,axiom,(
% 1.44/0.71    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.44/0.71  fof(f84,plain,(
% 1.44/0.71    ~v1_xboole_0(sK2) | ~v1_relat_1(sK2)),
% 1.44/0.71    inference(subsumption_resolution,[],[f83,f32])).
% 1.44/0.71  fof(f83,plain,(
% 1.44/0.71    ~v1_xboole_0(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)),
% 1.44/0.71    inference(resolution,[],[f36,f45])).
% 1.44/0.71  fof(f45,plain,(
% 1.44/0.71    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.71    inference(cnf_transformation,[],[f21])).
% 1.44/0.71  fof(f21,plain,(
% 1.44/0.71    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.44/0.71    inference(flattening,[],[f20])).
% 1.44/0.71  fof(f20,plain,(
% 1.44/0.71    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 1.44/0.71    inference(ennf_transformation,[],[f6])).
% 1.44/0.71  fof(f6,axiom,(
% 1.44/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).
% 1.44/0.71  fof(f120,plain,(
% 1.44/0.71    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 1.44/0.71    inference(resolution,[],[f34,f44])).
% 1.44/0.71  fof(f44,plain,(
% 1.44/0.71    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.44/0.71    inference(cnf_transformation,[],[f19])).
% 1.44/0.71  fof(f19,plain,(
% 1.44/0.71    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.44/0.71    inference(ennf_transformation,[],[f3])).
% 1.44/0.71  fof(f3,axiom,(
% 1.44/0.71    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.44/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.44/0.71  % SZS output end Proof for theBenchmark
% 1.44/0.71  % (29720)------------------------------
% 1.44/0.71  % (29720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.71  % (29720)Termination reason: Refutation
% 1.44/0.71  
% 1.44/0.71  % (29720)Memory used [KB]: 1918
% 1.44/0.71  % (29720)Time elapsed: 0.111 s
% 1.44/0.71  % (29720)------------------------------
% 1.44/0.71  % (29720)------------------------------
% 1.44/0.71  % (29483)Success in time 0.343 s
%------------------------------------------------------------------------------
