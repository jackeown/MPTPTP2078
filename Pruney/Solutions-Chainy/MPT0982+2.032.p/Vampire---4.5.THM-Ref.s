%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:31 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 490 expanded)
%              Number of leaves         :   14 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  310 (2720 expanded)
%              Number of equality atoms :   83 ( 780 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f652,plain,(
    $false ),
    inference(global_subsumption,[],[f116,f399,f651])).

fof(f651,plain,(
    r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f650,f398])).

fof(f398,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f375,f143])).

fof(f143,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f39,f142])).

fof(f142,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f140,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(f140,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f108,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f102,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0) ) ),
    inference(resolution,[],[f45,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f375,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f284,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f284,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f278,f244])).

fof(f244,plain,(
    k5_relat_1(sK3,sK4) = k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f104,f38])).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k4_relset_1(sK0,sK1,X4,X5,sK3,X3) = k5_relat_1(sK3,X3) ) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f278,plain,(
    m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f106,f38])).

fof(f106,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | m1_subset_1(k4_relset_1(sK0,sK1,X7,X8,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,X8))) ) ),
    inference(resolution,[],[f45,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f650,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f649,f405])).

fof(f405,plain,(
    v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f396,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f396,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f284,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f649,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f499,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f499,plain,(
    v5_relat_1(k5_relat_1(sK3,sK4),k2_relat_1(sK4)) ),
    inference(resolution,[],[f285,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f285,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4)))) ),
    inference(forward_demodulation,[],[f279,f245])).

fof(f245,plain,(
    k5_relat_1(sK3,sK4) = k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4) ),
    inference(resolution,[],[f104,f122])).

fof(f122,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) ),
    inference(resolution,[],[f97,f99])).

fof(f99,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f93,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f38,f55])).

fof(f97,plain,
    ( ~ v1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) ),
    inference(backward_demodulation,[],[f76,f95])).

fof(f95,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f89,f83])).

fof(f83,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f82,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f37,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f38,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f76,plain,
    ( ~ v1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f279,plain,(
    m1_subset_1(k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4)))) ),
    inference(resolution,[],[f106,f122])).

fof(f399,plain,(
    sK2 != k2_relat_1(sK4) ),
    inference(backward_demodulation,[],[f133,f398])).

fof(f133,plain,(
    k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f132,f99])).

fof(f132,plain,
    ( k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f131,f121])).

fof(f121,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f120,f117])).

fof(f117,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f42,f101])).

fof(f101,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f45,f53])).

fof(f42,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK3))
    | sK1 = k2_relat_1(sK3) ),
    inference(resolution,[],[f113,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f113,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f112,f109])).

fof(f109,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f107,f56])).

fof(f107,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f45,f55])).

fof(f112,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f105,f64])).

fof(f105,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f45,f66])).

fof(f131,plain,
    ( r1_tarski(sK1,k2_relat_1(sK3))
    | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f128,f109])).

fof(f128,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(sK1,k2_relat_1(sK3))
    | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f96,f43])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(sK1,k2_relat_1(X0))
      | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(X0,sK4))
      | ~ v1_relat_1(sK4) ) ),
    inference(backward_demodulation,[],[f78,f95])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(X0,sK4))
      | ~ v1_relat_1(sK4)
      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(X0,sK4))
      | ~ v1_relat_1(sK4)
      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(f40,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f116,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | sK2 = k2_relat_1(sK4) ),
    inference(resolution,[],[f111,f62])).

fof(f111,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f110,f99])).

fof(f110,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f91,f64])).

fof(f91,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f38,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.52  % (12671)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12664)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (12677)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (12661)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (12662)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (12681)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (12668)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (12665)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (12669)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (12663)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (12664)Refutation not found, incomplete strategy% (12664)------------------------------
% 0.22/0.53  % (12664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12680)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (12674)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (12670)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (12676)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (12672)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (12678)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (12660)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (12682)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (12664)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12664)Memory used [KB]: 10746
% 0.22/0.54  % (12664)Time elapsed: 0.109 s
% 0.22/0.54  % (12664)------------------------------
% 0.22/0.54  % (12664)------------------------------
% 0.22/0.54  % (12679)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (12673)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (12666)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (12658)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.49/0.55  % (12675)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.49/0.55  % (12683)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.49/0.55  % (12658)Refutation not found, incomplete strategy% (12658)------------------------------
% 1.49/0.55  % (12658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (12658)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (12658)Memory used [KB]: 10746
% 1.49/0.55  % (12658)Time elapsed: 0.139 s
% 1.49/0.55  % (12658)------------------------------
% 1.49/0.55  % (12658)------------------------------
% 1.49/0.56  % (12671)Refutation not found, incomplete strategy% (12671)------------------------------
% 1.49/0.56  % (12671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (12671)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (12671)Memory used [KB]: 6780
% 1.49/0.56  % (12671)Time elapsed: 0.132 s
% 1.49/0.56  % (12671)------------------------------
% 1.49/0.56  % (12671)------------------------------
% 1.49/0.56  % (12667)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.49/0.56  % (12663)Refutation found. Thanks to Tanya!
% 1.49/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f652,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(global_subsumption,[],[f116,f399,f651])).
% 1.49/0.56  fof(f651,plain,(
% 1.49/0.56    r1_tarski(sK2,k2_relat_1(sK4))),
% 1.49/0.56    inference(forward_demodulation,[],[f650,f398])).
% 1.49/0.56  fof(f398,plain,(
% 1.49/0.56    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.49/0.56    inference(forward_demodulation,[],[f375,f143])).
% 1.49/0.56  fof(f143,plain,(
% 1.49/0.56    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.49/0.56    inference(backward_demodulation,[],[f39,f142])).
% 1.49/0.56  fof(f142,plain,(
% 1.49/0.56    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.49/0.56    inference(subsumption_resolution,[],[f140,f36])).
% 1.49/0.56  fof(f36,plain,(
% 1.49/0.56    v1_funct_1(sK4)),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f18,plain,(
% 1.49/0.56    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.49/0.56    inference(flattening,[],[f17])).
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.49/0.56    inference(ennf_transformation,[],[f15])).
% 1.49/0.56  fof(f15,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.49/0.56    inference(negated_conjecture,[],[f14])).
% 1.49/0.56  fof(f14,conjecture,(
% 1.49/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 1.49/0.56  fof(f140,plain,(
% 1.49/0.56    ~v1_funct_1(sK4) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.49/0.56    inference(resolution,[],[f108,f38])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f108,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f102,f43])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    v1_funct_1(sK3)),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f102,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0)) )),
% 1.49/0.56    inference(resolution,[],[f45,f54])).
% 1.49/0.56  fof(f54,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f25])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.49/0.56    inference(flattening,[],[f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.49/0.56    inference(ennf_transformation,[],[f12])).
% 1.49/0.56  fof(f12,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f375,plain,(
% 1.49/0.56    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.49/0.56    inference(resolution,[],[f284,f53])).
% 1.49/0.56  fof(f53,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(ennf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.49/0.56  fof(f284,plain,(
% 1.49/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.49/0.56    inference(forward_demodulation,[],[f278,f244])).
% 1.49/0.56  fof(f244,plain,(
% 1.49/0.56    k5_relat_1(sK3,sK4) = k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)),
% 1.49/0.56    inference(resolution,[],[f104,f38])).
% 1.49/0.56  fof(f104,plain,(
% 1.49/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k4_relset_1(sK0,sK1,X4,X5,sK3,X3) = k5_relat_1(sK3,X3)) )),
% 1.49/0.56    inference(resolution,[],[f45,f65])).
% 1.49/0.56  fof(f65,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(flattening,[],[f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.49/0.56    inference(ennf_transformation,[],[f10])).
% 1.49/0.56  fof(f10,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.49/0.56  fof(f278,plain,(
% 1.49/0.56    m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.49/0.56    inference(resolution,[],[f106,f38])).
% 1.49/0.56  fof(f106,plain,(
% 1.49/0.56    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | m1_subset_1(k4_relset_1(sK0,sK1,X7,X8,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,X8)))) )),
% 1.49/0.56    inference(resolution,[],[f45,f67])).
% 1.49/0.56  fof(f67,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f35])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(flattening,[],[f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.49/0.56    inference(ennf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 1.49/0.56  fof(f650,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4))),
% 1.49/0.56    inference(subsumption_resolution,[],[f649,f405])).
% 1.49/0.56  fof(f405,plain,(
% 1.49/0.56    v1_relat_1(k5_relat_1(sK3,sK4))),
% 1.49/0.56    inference(subsumption_resolution,[],[f396,f56])).
% 1.49/0.56  fof(f56,plain,(
% 1.49/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.49/0.56  fof(f396,plain,(
% 1.49/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(k5_relat_1(sK3,sK4))),
% 1.49/0.56    inference(resolution,[],[f284,f55])).
% 1.49/0.56  fof(f55,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.49/0.56  fof(f649,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4))),
% 1.49/0.56    inference(resolution,[],[f499,f64])).
% 1.49/0.56  fof(f64,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.49/0.56  fof(f499,plain,(
% 1.49/0.56    v5_relat_1(k5_relat_1(sK3,sK4),k2_relat_1(sK4))),
% 1.49/0.56    inference(resolution,[],[f285,f66])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(ennf_transformation,[],[f16])).
% 1.49/0.56  fof(f16,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.49/0.56    inference(pure_predicate_removal,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.49/0.56  fof(f285,plain,(
% 1.49/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4))))),
% 1.49/0.56    inference(forward_demodulation,[],[f279,f245])).
% 1.49/0.56  fof(f245,plain,(
% 1.49/0.56    k5_relat_1(sK3,sK4) = k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4)),
% 1.49/0.56    inference(resolution,[],[f104,f122])).
% 1.49/0.56  fof(f122,plain,(
% 1.49/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4))))),
% 1.49/0.56    inference(resolution,[],[f97,f99])).
% 1.49/0.56  fof(f99,plain,(
% 1.49/0.56    v1_relat_1(sK4)),
% 1.49/0.56    inference(subsumption_resolution,[],[f93,f56])).
% 1.49/0.56  fof(f93,plain,(
% 1.49/0.56    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK4)),
% 1.49/0.56    inference(resolution,[],[f38,f55])).
% 1.49/0.56  fof(f97,plain,(
% 1.49/0.56    ~v1_relat_1(sK4) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4))))),
% 1.49/0.56    inference(backward_demodulation,[],[f76,f95])).
% 1.49/0.56  fof(f95,plain,(
% 1.49/0.56    sK1 = k1_relat_1(sK4)),
% 1.49/0.56    inference(forward_demodulation,[],[f89,f83])).
% 1.49/0.56  fof(f83,plain,(
% 1.49/0.56    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.49/0.56    inference(subsumption_resolution,[],[f82,f38])).
% 1.49/0.56  fof(f82,plain,(
% 1.49/0.56    sK1 = k1_relset_1(sK1,sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/0.56    inference(subsumption_resolution,[],[f81,f41])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    k1_xboole_0 != sK2),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/0.56    inference(resolution,[],[f37,f51])).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(flattening,[],[f19])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(ennf_transformation,[],[f11])).
% 1.49/0.56  fof(f11,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    v1_funct_2(sK4,sK1,sK2)),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f89,plain,(
% 1.49/0.56    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.49/0.56    inference(resolution,[],[f38,f59])).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f29])).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(ennf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.56  fof(f76,plain,(
% 1.49/0.56    ~v1_relat_1(sK4) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))),
% 1.49/0.56    inference(resolution,[],[f36,f58])).
% 1.49/0.56  fof(f58,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,axiom,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.49/0.56  fof(f279,plain,(
% 1.49/0.56    m1_subset_1(k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4))))),
% 1.49/0.56    inference(resolution,[],[f106,f122])).
% 1.49/0.56  fof(f399,plain,(
% 1.49/0.56    sK2 != k2_relat_1(sK4)),
% 1.49/0.56    inference(backward_demodulation,[],[f133,f398])).
% 1.49/0.56  fof(f133,plain,(
% 1.49/0.56    k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.49/0.56    inference(subsumption_resolution,[],[f132,f99])).
% 1.49/0.56  fof(f132,plain,(
% 1.49/0.56    k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4)),
% 1.49/0.56    inference(subsumption_resolution,[],[f131,f121])).
% 1.49/0.56  fof(f121,plain,(
% 1.49/0.56    ~r1_tarski(sK1,k2_relat_1(sK3))),
% 1.49/0.56    inference(subsumption_resolution,[],[f120,f117])).
% 1.49/0.56  fof(f117,plain,(
% 1.49/0.56    sK1 != k2_relat_1(sK3)),
% 1.49/0.56    inference(superposition,[],[f42,f101])).
% 1.49/0.56  fof(f101,plain,(
% 1.49/0.56    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.49/0.56    inference(resolution,[],[f45,f53])).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f120,plain,(
% 1.49/0.56    ~r1_tarski(sK1,k2_relat_1(sK3)) | sK1 = k2_relat_1(sK3)),
% 1.49/0.56    inference(resolution,[],[f113,f62])).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.49/0.56    inference(cnf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.56  fof(f113,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.49/0.56    inference(subsumption_resolution,[],[f112,f109])).
% 1.49/0.56  fof(f109,plain,(
% 1.49/0.56    v1_relat_1(sK3)),
% 1.49/0.56    inference(subsumption_resolution,[],[f107,f56])).
% 1.49/0.56  fof(f107,plain,(
% 1.49/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 1.49/0.56    inference(resolution,[],[f45,f55])).
% 1.49/0.56  fof(f112,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.49/0.56    inference(resolution,[],[f105,f64])).
% 1.49/0.56  fof(f105,plain,(
% 1.49/0.56    v5_relat_1(sK3,sK1)),
% 1.49/0.56    inference(resolution,[],[f45,f66])).
% 1.49/0.56  fof(f131,plain,(
% 1.49/0.56    r1_tarski(sK1,k2_relat_1(sK3)) | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4)),
% 1.49/0.56    inference(subsumption_resolution,[],[f128,f109])).
% 1.49/0.56  fof(f128,plain,(
% 1.49/0.56    ~v1_relat_1(sK3) | r1_tarski(sK1,k2_relat_1(sK3)) | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4)),
% 1.49/0.56    inference(resolution,[],[f96,f43])).
% 1.49/0.56  fof(f96,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(sK1,k2_relat_1(X0)) | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(X0,sK4)) | ~v1_relat_1(sK4)) )),
% 1.49/0.56    inference(backward_demodulation,[],[f78,f95])).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(X0,sK4)) | ~v1_relat_1(sK4) | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f77,f36])).
% 1.49/0.56  fof(f77,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(X0,sK4)) | ~v1_relat_1(sK4) | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))) )),
% 1.49/0.56    inference(resolution,[],[f40,f52])).
% 1.49/0.56  fof(f52,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f21])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    v2_funct_1(sK4)),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f116,plain,(
% 1.49/0.56    ~r1_tarski(sK2,k2_relat_1(sK4)) | sK2 = k2_relat_1(sK4)),
% 1.49/0.56    inference(resolution,[],[f111,f62])).
% 1.49/0.56  fof(f111,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(sK4),sK2)),
% 1.49/0.56    inference(subsumption_resolution,[],[f110,f99])).
% 1.49/0.56  fof(f110,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 1.49/0.56    inference(resolution,[],[f91,f64])).
% 1.49/0.56  fof(f91,plain,(
% 1.49/0.56    v5_relat_1(sK4,sK2)),
% 1.49/0.56    inference(resolution,[],[f38,f66])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (12663)------------------------------
% 1.49/0.56  % (12663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (12663)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (12663)Memory used [KB]: 7036
% 1.49/0.56  % (12663)Time elapsed: 0.150 s
% 1.49/0.56  % (12663)------------------------------
% 1.49/0.56  % (12663)------------------------------
% 1.49/0.56  % (12657)Success in time 0.202 s
%------------------------------------------------------------------------------
