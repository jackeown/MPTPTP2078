%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 (3807 expanded)
%              Number of leaves         :    8 ( 713 expanded)
%              Depth                    :   29
%              Number of atoms          :  287 (26910 expanded)
%              Number of equality atoms :   98 (7092 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(subsumption_resolution,[],[f190,f188])).

fof(f188,plain,(
    v2_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f159,f185])).

fof(f185,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f164,f184])).

fof(f184,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f176,f162])).

fof(f162,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f145,f152])).

fof(f152,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f22,f143])).

fof(f143,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f142,f139])).

fof(f139,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f132,f103])).

fof(f103,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f64,f72])).

fof(f72,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X0,X1,X3) = X1
                & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
             => ( ( v2_funct_1(X4)
                  & v2_funct_1(X3) )
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f64,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f63,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f24,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f24,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f132,plain,
    ( sK1 != k1_relat_1(sK4)
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f131,f89])).

fof(f89,plain,(
    sK1 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f86,f27])).

fof(f27,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f131,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f130,f28])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f130,plain,
    ( ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f129,f90])).

fof(f90,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f88,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f88,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f129,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f128,f23])).

fof(f23,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f128,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f126,f74])).

fof(f74,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f73,f34])).

fof(f73,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f25,f31])).

fof(f126,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f125,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f125,plain,(
    v2_funct_1(k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f26,f124])).

fof(f124,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f121,f25])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK3,sK4) = k1_partfun1(sK0,sK1,X0,X1,sK3,sK4) ) ),
    inference(resolution,[],[f118,f30])).

fof(f118,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k5_relat_1(sK3,sK4) = k1_partfun1(X4,X5,X6,X7,sK3,sK4) ) ),
    inference(resolution,[],[f49,f28])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ) ),
    inference(resolution,[],[f23,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f26,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f142,plain,
    ( k1_xboole_0 = sK2
    | ~ v2_funct_1(sK3) ),
    inference(resolution,[],[f141,f21])).

fof(f21,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f141,plain,
    ( v2_funct_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( sK1 != sK1
    | v2_funct_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f137,f103])).

fof(f137,plain,
    ( sK1 != k1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(forward_demodulation,[],[f136,f89])).

fof(f136,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f135,f28])).

fof(f135,plain,
    ( ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f134,f90])).

fof(f134,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f133,f23])).

fof(f133,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f127,f74])).

fof(f127,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(resolution,[],[f125,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f145,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f25,f143])).

fof(f176,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(resolution,[],[f161,f44])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f161,plain,(
    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f144,f152])).

fof(f144,plain,(
    v1_funct_2(sK4,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f24,f143])).

fof(f164,plain,(
    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f147,f152])).

fof(f147,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f72,f143])).

fof(f159,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f132,f152])).

fof(f190,plain,(
    ~ v2_funct_1(sK3) ),
    inference(resolution,[],[f189,f21])).

fof(f189,plain,(
    v2_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f186])).

fof(f186,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_funct_1(sK4) ),
    inference(backward_demodulation,[],[f160,f185])).

fof(f160,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(backward_demodulation,[],[f137,f152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:09:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (3002)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (3005)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (2997)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (2998)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (3010)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (3003)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (3006)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (3010)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (3012)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f188])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    v2_funct_1(sK3)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f187])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | v2_funct_1(sK3)),
% 0.22/0.52    inference(backward_demodulation,[],[f159,f185])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK4)),
% 0.22/0.52    inference(backward_demodulation,[],[f164,f184])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f176,f162])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f145,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f22,f143])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    k1_xboole_0 = sK2),
% 0.22/0.52    inference(subsumption_resolution,[],[f142,f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    v2_funct_1(sK3) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    sK1 != sK1 | v2_funct_1(sK3) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f132,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f64,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f25,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & (k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(subsumption_resolution,[],[f63,f25])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.22/0.52    inference(resolution,[],[f24,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v1_funct_2(sK4,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    sK1 != k1_relat_1(sK4) | v2_funct_1(sK3)),
% 0.22/0.52    inference(forward_demodulation,[],[f131,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK3)),
% 0.22/0.52    inference(forward_demodulation,[],[f86,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f30,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f129,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f30,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f128,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    v1_funct_1(sK4)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ~v1_funct_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f126,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    v1_relat_1(sK4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f73,f34])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f25,f31])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f125,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    v2_funct_1(k5_relat_1(sK3,sK4))),
% 0.22/0.52    inference(backward_demodulation,[],[f26,f124])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.22/0.52    inference(resolution,[],[f121,f25])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK3,sK4) = k1_partfun1(sK0,sK1,X0,X1,sK3,sK4)) )),
% 0.22/0.52    inference(resolution,[],[f118,f30])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k5_relat_1(sK3,sK4) = k1_partfun1(X4,X5,X6,X7,sK3,sK4)) )),
% 0.22/0.52    inference(resolution,[],[f49,f28])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4)) )),
% 0.22/0.52    inference(resolution,[],[f23,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | ~v2_funct_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f141,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ~v2_funct_1(sK4) | ~v2_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    v2_funct_1(sK4) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f140])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    sK1 != sK1 | v2_funct_1(sK4) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f137,f103])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    sK1 != k1_relat_1(sK4) | v2_funct_1(sK4)),
% 0.22/0.52    inference(forward_demodulation,[],[f136,f89])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f28])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f134,f90])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f133,f23])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ~v1_funct_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f127,f74])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f125,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f25,f143])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.22/0.52    inference(resolution,[],[f161,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f144,f152])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    v1_funct_2(sK4,sK1,k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f24,f143])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.22/0.52    inference(backward_demodulation,[],[f147,f152])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4)),
% 0.22/0.52    inference(backward_demodulation,[],[f72,f143])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    k1_xboole_0 != k1_relat_1(sK4) | v2_funct_1(sK3)),
% 0.22/0.52    inference(backward_demodulation,[],[f132,f152])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ~v2_funct_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f189,f21])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    v2_funct_1(sK4)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f186])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | v2_funct_1(sK4)),
% 0.22/0.52    inference(backward_demodulation,[],[f160,f185])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    k1_xboole_0 != k1_relat_1(sK4) | v2_funct_1(sK4)),
% 0.22/0.52    inference(backward_demodulation,[],[f137,f152])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (3010)------------------------------
% 0.22/0.52  % (3010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3010)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (3010)Memory used [KB]: 1663
% 0.22/0.52  % (3010)Time elapsed: 0.087 s
% 0.22/0.52  % (3010)------------------------------
% 0.22/0.52  % (3010)------------------------------
% 0.22/0.53  % (2996)Success in time 0.162 s
%------------------------------------------------------------------------------
