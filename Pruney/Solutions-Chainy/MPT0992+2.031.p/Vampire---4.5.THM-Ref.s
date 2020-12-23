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
% DateTime   : Thu Dec  3 13:03:14 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  120 (4697 expanded)
%              Number of leaves         :   16 ( 880 expanded)
%              Depth                    :   26
%              Number of atoms          :  302 (23669 expanded)
%              Number of equality atoms :   84 (5352 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1622,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1614,f1619])).

fof(f1619,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1008,f1618])).

fof(f1618,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f1617,f1610])).

fof(f1610,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f1609])).

fof(f1609,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f39,f746])).

fof(f746,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f745,f363])).

fof(f363,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f147,f358])).

fof(f358,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f229,f43])).

fof(f43,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f229,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_relat_1(k7_relat_1(sK3,X0)) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f228,f90])).

fof(f90,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(k7_relat_1(sK3,X0)) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f67,f208])).

fof(f208,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f85,f92])).

fof(f92,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f42,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f85,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f41,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f41,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f147,plain,(
    ! [X2] : m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) ),
    inference(subsumption_resolution,[],[f146,f103])).

fof(f103,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f90,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f146,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X2))
      | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) ) ),
    inference(subsumption_resolution,[],[f141,f100])).

fof(f100,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f95,f97])).

fof(f97,plain,(
    ! [X2] : k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK3)
      | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f42,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f95,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f141,plain,(
    ! [X2] :
      ( ~ v1_funct_1(k7_relat_1(sK3,X2))
      | ~ v1_relat_1(k7_relat_1(sK3,X2))
      | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) ) ),
    inference(resolution,[],[f134,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f134,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f133,f103])).

fof(f133,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f125,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f125,plain,(
    ! [X9] : v5_relat_1(k7_relat_1(sK3,X9),sK1) ),
    inference(resolution,[],[f99,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f99,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f96,f97])).

fof(f96,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f88,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f745,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f742,f100])).

fof(f742,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(resolution,[],[f364,f102])).

fof(f102,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    inference(forward_demodulation,[],[f98,f97])).

fof(f98,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    inference(backward_demodulation,[],[f38,f97])).

fof(f38,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f364,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f145,f358])).

fof(f145,plain,(
    ! [X1] : v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) ),
    inference(subsumption_resolution,[],[f144,f103])).

fof(f144,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X1))
      | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) ) ),
    inference(subsumption_resolution,[],[f140,f100])).

fof(f140,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k7_relat_1(sK3,X1))
      | ~ v1_relat_1(k7_relat_1(sK3,X1))
      | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) ) ),
    inference(resolution,[],[f134,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f39,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f1617,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f1613,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1613,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK0 = sK2 ),
    inference(backward_demodulation,[],[f83,f1610])).

fof(f83,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f43,f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1008,plain,(
    ~ v1_funct_2(k1_xboole_0,sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f895,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f895,plain,(
    ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f860,f864])).

fof(f864,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f863,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f863,plain,(
    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f862,f746])).

fof(f862,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f861,f55])).

fof(f861,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f756,f73])).

fof(f756,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f108,f746])).

fof(f108,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f94,f52])).

fof(f94,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f860,plain,(
    ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f859,f746])).

fof(f859,plain,(
    ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    inference(subsumption_resolution,[],[f858,f856])).

fof(f856,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f753,f73])).

fof(f753,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f99,f746])).

fof(f858,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    inference(forward_demodulation,[],[f857,f73])).

fof(f857,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    inference(subsumption_resolution,[],[f754,f100])).

fof(f754,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f102,f746])).

fof(f1614,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f887,f1610])).

fof(f887,plain,(
    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f747,f864])).

fof(f747,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f41,f746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:33:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (30169)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (30170)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (30175)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (30171)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (30183)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (30185)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (30166)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (30176)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (30173)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (30168)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (30184)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (30186)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (30177)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (30178)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (30187)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (30188)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (30190)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (30180)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (30179)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (30172)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (30174)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (30191)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (30182)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.54  % (30167)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (30181)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.50/0.56  % (30189)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.50/0.56  % (30171)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f1622,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(subsumption_resolution,[],[f1614,f1619])).
% 1.50/0.56  fof(f1619,plain,(
% 1.50/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.50/0.56    inference(backward_demodulation,[],[f1008,f1618])).
% 1.50/0.56  fof(f1618,plain,(
% 1.50/0.56    k1_xboole_0 = sK2),
% 1.50/0.56    inference(forward_demodulation,[],[f1617,f1610])).
% 1.50/0.56  fof(f1610,plain,(
% 1.50/0.56    k1_xboole_0 = sK0),
% 1.50/0.56    inference(trivial_inequality_removal,[],[f1609])).
% 1.50/0.56  fof(f1609,plain,(
% 1.50/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.50/0.56    inference(superposition,[],[f39,f746])).
% 1.50/0.56  fof(f746,plain,(
% 1.50/0.56    k1_xboole_0 = sK1),
% 1.50/0.56    inference(subsumption_resolution,[],[f745,f363])).
% 1.50/0.56  fof(f363,plain,(
% 1.50/0.56    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k1_xboole_0 = sK1),
% 1.50/0.56    inference(superposition,[],[f147,f358])).
% 1.50/0.56  fof(f358,plain,(
% 1.50/0.56    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1),
% 1.50/0.56    inference(resolution,[],[f229,f43])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    r1_tarski(sK2,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.50/0.56    inference(flattening,[],[f21])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.50/0.56    inference(ennf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.50/0.56    inference(negated_conjecture,[],[f18])).
% 1.50/0.56  fof(f18,conjecture,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.50/0.56  fof(f229,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | k1_xboole_0 = sK1) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f228,f90])).
% 1.50/0.56  fof(f90,plain,(
% 1.50/0.56    v1_relat_1(sK3)),
% 1.50/0.56    inference(resolution,[],[f42,f58])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f228,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK3) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | k1_xboole_0 = sK1) )),
% 1.50/0.56    inference(superposition,[],[f67,f208])).
% 1.50/0.56  fof(f208,plain,(
% 1.50/0.56    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.50/0.56    inference(superposition,[],[f85,f92])).
% 1.50/0.56  fof(f92,plain,(
% 1.50/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.50/0.56    inference(resolution,[],[f42,f69])).
% 1.50/0.56  fof(f69,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f13])).
% 1.50/0.56  fof(f13,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.56  fof(f85,plain,(
% 1.50/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.50/0.56    inference(subsumption_resolution,[],[f84,f42])).
% 1.50/0.56  fof(f84,plain,(
% 1.50/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.56    inference(resolution,[],[f41,f64])).
% 1.50/0.56  fof(f64,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(flattening,[],[f28])).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f14])).
% 1.50/0.56  fof(f14,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f67,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f33])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(flattening,[],[f32])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.50/0.56  fof(f147,plain,(
% 1.50/0.56    ( ! [X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f146,f103])).
% 1.50/0.56  fof(f103,plain,(
% 1.50/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.50/0.56    inference(resolution,[],[f90,f68])).
% 1.50/0.56  fof(f68,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.50/0.56  fof(f146,plain,(
% 1.50/0.56    ( ! [X2] : (~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f141,f100])).
% 1.50/0.56  fof(f100,plain,(
% 1.50/0.56    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.50/0.56    inference(backward_demodulation,[],[f95,f97])).
% 1.50/0.56  fof(f97,plain,(
% 1.50/0.56    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f89,f40])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    v1_funct_1(sK3)),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f89,plain,(
% 1.50/0.56    ( ! [X2] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) )),
% 1.50/0.56    inference(resolution,[],[f42,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.50/0.56    inference(flattening,[],[f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.50/0.56    inference(ennf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.50/0.56  fof(f95,plain,(
% 1.50/0.56    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f87,f40])).
% 1.50/0.56  fof(f87,plain,(
% 1.50/0.56    ( ! [X0] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.50/0.56    inference(resolution,[],[f42,f44])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.50/0.56    inference(flattening,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.50/0.56    inference(ennf_transformation,[],[f15])).
% 1.50/0.56  fof(f15,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.50/0.56  fof(f141,plain,(
% 1.50/0.56    ( ! [X2] : (~v1_funct_1(k7_relat_1(sK3,X2)) | ~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) )),
% 1.50/0.56    inference(resolution,[],[f134,f66])).
% 1.50/0.56  fof(f66,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(flattening,[],[f30])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.56    inference(ennf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,axiom,(
% 1.50/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.50/0.56  fof(f134,plain,(
% 1.50/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f133,f103])).
% 1.50/0.56  fof(f133,plain,(
% 1.50/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.50/0.56    inference(resolution,[],[f125,f71])).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f36])).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.50/0.56  fof(f125,plain,(
% 1.50/0.56    ( ! [X9] : (v5_relat_1(k7_relat_1(sK3,X9),sK1)) )),
% 1.50/0.56    inference(resolution,[],[f99,f72])).
% 1.50/0.56  fof(f72,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f37])).
% 1.50/0.56  fof(f37,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.50/0.56    inference(pure_predicate_removal,[],[f12])).
% 1.50/0.56  fof(f12,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.50/0.56  fof(f99,plain,(
% 1.50/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.50/0.56    inference(backward_demodulation,[],[f96,f97])).
% 1.50/0.56  fof(f96,plain,(
% 1.50/0.56    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f88,f40])).
% 1.50/0.56  fof(f88,plain,(
% 1.50/0.56    ( ! [X1] : (~v1_funct_1(sK3) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.50/0.56    inference(resolution,[],[f42,f45])).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f24])).
% 1.50/0.56  fof(f745,plain,(
% 1.50/0.56    k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.50/0.56    inference(subsumption_resolution,[],[f742,f100])).
% 1.50/0.56  fof(f742,plain,(
% 1.50/0.56    k1_xboole_0 = sK1 | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.50/0.56    inference(resolution,[],[f364,f102])).
% 1.50/0.56  fof(f102,plain,(
% 1.50/0.56    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.50/0.56    inference(forward_demodulation,[],[f101,f97])).
% 1.50/0.56  fof(f101,plain,(
% 1.50/0.56    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.50/0.56    inference(forward_demodulation,[],[f98,f97])).
% 1.50/0.56  fof(f98,plain,(
% 1.50/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.50/0.56    inference(backward_demodulation,[],[f38,f97])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f364,plain,(
% 1.50/0.56    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1),
% 1.50/0.56    inference(superposition,[],[f145,f358])).
% 1.50/0.56  fof(f145,plain,(
% 1.50/0.56    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f144,f103])).
% 1.50/0.56  fof(f144,plain,(
% 1.50/0.56    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f140,f100])).
% 1.50/0.56  fof(f140,plain,(
% 1.50/0.56    ( ! [X1] : (~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) )),
% 1.50/0.56    inference(resolution,[],[f134,f65])).
% 1.50/0.56  fof(f65,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f31])).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f1617,plain,(
% 1.50/0.56    sK0 = sK2),
% 1.50/0.56    inference(subsumption_resolution,[],[f1613,f55])).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.50/0.56  fof(f1613,plain,(
% 1.50/0.56    ~r1_tarski(k1_xboole_0,sK2) | sK0 = sK2),
% 1.50/0.56    inference(backward_demodulation,[],[f83,f1610])).
% 1.50/0.56  fof(f83,plain,(
% 1.50/0.56    ~r1_tarski(sK0,sK2) | sK0 = sK2),
% 1.50/0.56    inference(resolution,[],[f43,f52])).
% 1.50/0.56  fof(f52,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.56  fof(f1008,plain,(
% 1.50/0.56    ~v1_funct_2(k1_xboole_0,sK2,k1_xboole_0)),
% 1.50/0.56    inference(forward_demodulation,[],[f895,f53])).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,axiom,(
% 1.50/0.56    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 1.50/0.56  fof(f895,plain,(
% 1.50/0.56    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,k1_xboole_0)),
% 1.50/0.56    inference(backward_demodulation,[],[f860,f864])).
% 1.50/0.56  fof(f864,plain,(
% 1.50/0.56    k1_xboole_0 = sK3),
% 1.50/0.56    inference(forward_demodulation,[],[f863,f73])).
% 1.50/0.56  fof(f73,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.56    inference(equality_resolution,[],[f49])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.56  fof(f863,plain,(
% 1.50/0.56    sK3 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.50/0.56    inference(forward_demodulation,[],[f862,f746])).
% 1.50/0.56  fof(f862,plain,(
% 1.50/0.56    sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.50/0.56    inference(subsumption_resolution,[],[f861,f55])).
% 1.50/0.56  fof(f861,plain,(
% 1.50/0.56    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.50/0.56    inference(forward_demodulation,[],[f756,f73])).
% 1.50/0.56  fof(f756,plain,(
% 1.50/0.56    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.50/0.56    inference(backward_demodulation,[],[f108,f746])).
% 1.50/0.56  fof(f108,plain,(
% 1.50/0.56    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.50/0.56    inference(resolution,[],[f94,f52])).
% 1.50/0.56  fof(f94,plain,(
% 1.50/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.50/0.56    inference(resolution,[],[f42,f57])).
% 1.50/0.56  fof(f57,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.50/0.56  fof(f860,plain,(
% 1.50/0.56    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)),
% 1.50/0.56    inference(forward_demodulation,[],[f859,f746])).
% 1.50/0.56  fof(f859,plain,(
% 1.50/0.56    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.50/0.56    inference(subsumption_resolution,[],[f858,f856])).
% 1.50/0.56  fof(f856,plain,(
% 1.50/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.50/0.56    inference(forward_demodulation,[],[f753,f73])).
% 1.50/0.56  fof(f753,plain,(
% 1.50/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))) )),
% 1.50/0.56    inference(backward_demodulation,[],[f99,f746])).
% 1.50/0.56  fof(f858,plain,(
% 1.50/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.50/0.56    inference(forward_demodulation,[],[f857,f73])).
% 1.50/0.56  fof(f857,plain,(
% 1.50/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.50/0.56    inference(subsumption_resolution,[],[f754,f100])).
% 1.50/0.56  fof(f754,plain,(
% 1.50/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(k7_relat_1(sK3,sK2))),
% 1.50/0.56    inference(backward_demodulation,[],[f102,f746])).
% 1.50/0.56  fof(f1614,plain,(
% 1.50/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.50/0.56    inference(backward_demodulation,[],[f887,f1610])).
% 1.50/0.56  fof(f887,plain,(
% 1.50/0.56    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 1.50/0.56    inference(backward_demodulation,[],[f747,f864])).
% 1.50/0.56  fof(f747,plain,(
% 1.50/0.56    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.50/0.56    inference(backward_demodulation,[],[f41,f746])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (30171)------------------------------
% 1.50/0.56  % (30171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (30171)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (30171)Memory used [KB]: 6908
% 1.50/0.56  % (30171)Time elapsed: 0.167 s
% 1.50/0.56  % (30171)------------------------------
% 1.50/0.56  % (30171)------------------------------
% 1.65/0.58  % (30164)Success in time 0.227 s
%------------------------------------------------------------------------------
