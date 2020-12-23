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
% DateTime   : Thu Dec  3 13:02:28 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 715 expanded)
%              Number of leaves         :   20 ( 135 expanded)
%              Depth                    :   24
%              Number of atoms          :  478 (5024 expanded)
%              Number of equality atoms :  162 (1647 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1804,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1803,f59])).

fof(f59,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1803,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f1585,f1773])).

fof(f1773,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(backward_demodulation,[],[f231,f1768])).

fof(f1768,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f1512,f256])).

fof(f256,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f235,f86])).

fof(f86,plain,(
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

fof(f235,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f234,f196])).

fof(f196,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f234,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f197,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f197,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f53,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1512,plain,(
    r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1471,f98])).

fof(f98,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1471,plain,
    ( sK0 != k1_relat_1(k6_partfun1(sK0))
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f389,f1448])).

fof(f1448,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1447,f916])).

fof(f916,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f907,f905])).

fof(f905,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f900,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f900,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f211,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f211,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f204,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f204,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(resolution,[],[f53,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f907,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f281,f905])).

fof(f281,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f279,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f279,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f55,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f55,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1447,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1446,f53])).

fof(f1446,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1445,f51])).

fof(f1445,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1444,f62])).

fof(f1444,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1443,f60])).

fof(f1443,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f96,f905])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f389,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f385,f196])).

fof(f385,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(resolution,[],[f347,f51])).

fof(f347,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | sK0 != k1_relat_1(k5_relat_1(sK2,X1))
      | ~ v1_relat_1(X1)
      | r1_tarski(sK1,k1_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f336,f345])).

fof(f345,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f193,f261])).

fof(f261,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f87])).

fof(f193,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f191,f97])).

fof(f97,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f63])).

fof(f67,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f191,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f140,f189])).

fof(f189,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f188,f58])).

fof(f58,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f188,plain,
    ( k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f187,f56])).

fof(f56,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f187,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f186,f54])).

fof(f54,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f186,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f185,f62])).

fof(f185,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f174,f60])).

fof(f174,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(resolution,[],[f61,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f140,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) ),
    inference(subsumption_resolution,[],[f130,f60])).

fof(f130,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) ),
    inference(resolution,[],[f56,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f336,plain,(
    ! [X1] :
      ( sK0 != k1_relat_1(k5_relat_1(sK2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f330,f261])).

fof(f330,plain,(
    ! [X1] :
      ( sK0 != k1_relat_1(k5_relat_1(sK2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2)
      | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f154,f326])).

fof(f326,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f183,f261])).

fof(f183,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f181,f97])).

fof(f181,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f142,f179])).

fof(f179,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f178,f58])).

fof(f178,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f177,f56])).

fof(f177,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f176,f54])).

fof(f176,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f175,f62])).

fof(f175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f173,f60])).

fof(f173,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f61,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f142,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f132,f60])).

fof(f132,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(resolution,[],[f56,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f154,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2)
      | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1))
      | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f60,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f231,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f196,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f69,f63])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1585,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(forward_demodulation,[],[f1479,f334])).

fof(f334,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f319,f333])).

fof(f333,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f328,f261])).

fof(f328,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f138,f326])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f128,f60])).

fof(f128,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f56,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f319,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) ),
    inference(resolution,[],[f282,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f68,f63])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f282,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f261,f145])).

fof(f145,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1479,plain,(
    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(backward_demodulation,[],[f711,f1448])).

fof(f711,plain,(
    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(resolution,[],[f705,f196])).

fof(f705,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X7)) = k5_relat_1(k6_partfun1(sK1),X7) ) ),
    inference(forward_demodulation,[],[f702,f189])).

fof(f702,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X7) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X7)) ) ),
    inference(resolution,[],[f284,f282])).

fof(f284,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f261,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (22869)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (22878)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (22859)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (22863)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (22877)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (22855)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (22864)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (22870)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (22858)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (22869)Refutation not found, incomplete strategy% (22869)------------------------------
% 0.21/0.53  % (22869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22869)Memory used [KB]: 10746
% 0.21/0.53  % (22869)Time elapsed: 0.115 s
% 0.21/0.53  % (22869)------------------------------
% 0.21/0.53  % (22869)------------------------------
% 0.21/0.53  % (22857)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (22861)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (22854)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (22875)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (22862)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (22879)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (22866)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (22853)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (22871)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (22872)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (22868)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (22856)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (22881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (22867)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (22865)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (22876)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (22860)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (22882)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (22874)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (22873)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.57  % (22880)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.76/0.61  % (22870)Refutation found. Thanks to Tanya!
% 1.76/0.61  % SZS status Theorem for theBenchmark
% 1.76/0.61  % SZS output start Proof for theBenchmark
% 1.76/0.61  fof(f1804,plain,(
% 1.76/0.61    $false),
% 1.76/0.61    inference(subsumption_resolution,[],[f1803,f59])).
% 1.76/0.61  fof(f59,plain,(
% 1.76/0.61    sK3 != k2_funct_1(sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f24,plain,(
% 1.76/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.76/0.61    inference(flattening,[],[f23])).
% 1.76/0.61  fof(f23,plain,(
% 1.76/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.76/0.61    inference(ennf_transformation,[],[f22])).
% 1.76/0.61  fof(f22,negated_conjecture,(
% 1.76/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.61    inference(negated_conjecture,[],[f21])).
% 1.76/0.61  fof(f21,conjecture,(
% 1.76/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.76/0.61  fof(f1803,plain,(
% 1.76/0.61    sK3 = k2_funct_1(sK2)),
% 1.76/0.61    inference(backward_demodulation,[],[f1585,f1773])).
% 1.76/0.61  fof(f1773,plain,(
% 1.76/0.61    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.76/0.61    inference(backward_demodulation,[],[f231,f1768])).
% 1.76/0.61  fof(f1768,plain,(
% 1.76/0.61    sK1 = k1_relat_1(sK3)),
% 1.76/0.61    inference(resolution,[],[f1512,f256])).
% 1.76/0.61  fof(f256,plain,(
% 1.76/0.61    ~r1_tarski(sK1,k1_relat_1(sK3)) | sK1 = k1_relat_1(sK3)),
% 1.76/0.61    inference(resolution,[],[f235,f86])).
% 1.76/0.61  fof(f86,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.76/0.61    inference(cnf_transformation,[],[f1])).
% 1.76/0.61  fof(f1,axiom,(
% 1.76/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.76/0.61  fof(f235,plain,(
% 1.76/0.61    r1_tarski(k1_relat_1(sK3),sK1)),
% 1.76/0.61    inference(subsumption_resolution,[],[f234,f196])).
% 1.76/0.61  fof(f196,plain,(
% 1.76/0.61    v1_relat_1(sK3)),
% 1.76/0.61    inference(resolution,[],[f53,f87])).
% 1.76/0.61  fof(f87,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f41])).
% 1.76/0.61  fof(f41,plain,(
% 1.76/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(ennf_transformation,[],[f13])).
% 1.76/0.61  fof(f13,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.76/0.61  fof(f53,plain,(
% 1.76/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f234,plain,(
% 1.76/0.61    ~v1_relat_1(sK3) | r1_tarski(k1_relat_1(sK3),sK1)),
% 1.76/0.61    inference(resolution,[],[f197,f83])).
% 1.76/0.61  fof(f83,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f40])).
% 1.76/0.61  fof(f40,plain,(
% 1.76/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.76/0.61    inference(ennf_transformation,[],[f2])).
% 1.76/0.61  fof(f2,axiom,(
% 1.76/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.76/0.61  fof(f197,plain,(
% 1.76/0.61    v4_relat_1(sK3,sK1)),
% 1.76/0.61    inference(resolution,[],[f53,f88])).
% 1.76/0.61  fof(f88,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f42])).
% 1.76/0.61  fof(f42,plain,(
% 1.76/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(ennf_transformation,[],[f14])).
% 1.76/0.61  fof(f14,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.76/0.61  fof(f1512,plain,(
% 1.76/0.61    r1_tarski(sK1,k1_relat_1(sK3))),
% 1.76/0.61    inference(subsumption_resolution,[],[f1471,f98])).
% 1.76/0.61  fof(f98,plain,(
% 1.76/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.76/0.61    inference(definition_unfolding,[],[f66,f63])).
% 1.76/0.61  fof(f63,plain,(
% 1.76/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f19])).
% 1.76/0.61  fof(f19,axiom,(
% 1.76/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.76/0.61  fof(f66,plain,(
% 1.76/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f4])).
% 1.76/0.61  fof(f4,axiom,(
% 1.76/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.76/0.61  fof(f1471,plain,(
% 1.76/0.61    sK0 != k1_relat_1(k6_partfun1(sK0)) | r1_tarski(sK1,k1_relat_1(sK3))),
% 1.76/0.61    inference(backward_demodulation,[],[f389,f1448])).
% 1.76/0.61  fof(f1448,plain,(
% 1.76/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.76/0.61    inference(resolution,[],[f1447,f916])).
% 1.76/0.61  fof(f916,plain,(
% 1.76/0.61    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.76/0.61    inference(forward_demodulation,[],[f907,f905])).
% 1.76/0.61  fof(f905,plain,(
% 1.76/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.76/0.61    inference(subsumption_resolution,[],[f900,f60])).
% 1.76/0.61  fof(f60,plain,(
% 1.76/0.61    v1_funct_1(sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f900,plain,(
% 1.76/0.61    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.76/0.61    inference(resolution,[],[f211,f62])).
% 1.76/0.61  fof(f62,plain,(
% 1.76/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f211,plain,(
% 1.76/0.61    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(X5) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 1.76/0.61    inference(subsumption_resolution,[],[f204,f51])).
% 1.76/0.61  fof(f51,plain,(
% 1.76/0.61    v1_funct_1(sK3)),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f204,plain,(
% 1.76/0.61    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK3) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 1.76/0.61    inference(resolution,[],[f53,f94])).
% 1.76/0.61  fof(f94,plain,(
% 1.76/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f48])).
% 1.76/0.61  fof(f48,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.61    inference(flattening,[],[f47])).
% 1.76/0.61  fof(f47,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.61    inference(ennf_transformation,[],[f18])).
% 1.76/0.61  fof(f18,axiom,(
% 1.76/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.76/0.61  fof(f907,plain,(
% 1.76/0.61    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.76/0.61    inference(backward_demodulation,[],[f281,f905])).
% 1.76/0.61  fof(f281,plain,(
% 1.76/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.76/0.61    inference(subsumption_resolution,[],[f279,f65])).
% 1.76/0.61  fof(f65,plain,(
% 1.76/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f17])).
% 1.76/0.61  fof(f17,axiom,(
% 1.76/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.76/0.61  fof(f279,plain,(
% 1.76/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.76/0.61    inference(resolution,[],[f55,f93])).
% 1.76/0.61  fof(f93,plain,(
% 1.76/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f46])).
% 1.76/0.61  fof(f46,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(flattening,[],[f45])).
% 1.76/0.61  fof(f45,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.76/0.61    inference(ennf_transformation,[],[f15])).
% 1.76/0.61  fof(f15,axiom,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.76/0.61  fof(f55,plain,(
% 1.76/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f1447,plain,(
% 1.76/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.76/0.61    inference(subsumption_resolution,[],[f1446,f53])).
% 1.76/0.61  fof(f1446,plain,(
% 1.76/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.61    inference(subsumption_resolution,[],[f1445,f51])).
% 1.76/0.61  fof(f1445,plain,(
% 1.76/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.61    inference(subsumption_resolution,[],[f1444,f62])).
% 1.76/0.61  fof(f1444,plain,(
% 1.76/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.61    inference(subsumption_resolution,[],[f1443,f60])).
% 1.76/0.61  fof(f1443,plain,(
% 1.76/0.61    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.61    inference(superposition,[],[f96,f905])).
% 1.76/0.61  fof(f96,plain,(
% 1.76/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f50])).
% 1.76/0.61  fof(f50,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.61    inference(flattening,[],[f49])).
% 1.76/0.61  fof(f49,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.61    inference(ennf_transformation,[],[f16])).
% 1.76/0.61  fof(f16,axiom,(
% 1.76/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.76/0.61  fof(f389,plain,(
% 1.76/0.61    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | r1_tarski(sK1,k1_relat_1(sK3))),
% 1.76/0.61    inference(subsumption_resolution,[],[f385,f196])).
% 1.76/0.61  fof(f385,plain,(
% 1.76/0.61    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3) | r1_tarski(sK1,k1_relat_1(sK3))),
% 1.76/0.61    inference(resolution,[],[f347,f51])).
% 1.76/0.61  fof(f347,plain,(
% 1.76/0.61    ( ! [X1] : (~v1_funct_1(X1) | sK0 != k1_relat_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(X1) | r1_tarski(sK1,k1_relat_1(X1))) )),
% 1.76/0.61    inference(backward_demodulation,[],[f336,f345])).
% 1.76/0.61  fof(f345,plain,(
% 1.76/0.61    sK1 = k2_relat_1(sK2)),
% 1.76/0.61    inference(resolution,[],[f193,f261])).
% 1.76/0.61  fof(f261,plain,(
% 1.76/0.61    v1_relat_1(sK2)),
% 1.76/0.61    inference(resolution,[],[f62,f87])).
% 1.76/0.61  fof(f193,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | sK1 = k2_relat_1(sK2)),
% 1.76/0.61    inference(forward_demodulation,[],[f191,f97])).
% 1.76/0.61  fof(f97,plain,(
% 1.76/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.76/0.61    inference(definition_unfolding,[],[f67,f63])).
% 1.76/0.61  fof(f67,plain,(
% 1.76/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f4])).
% 1.76/0.61  fof(f191,plain,(
% 1.76/0.61    k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2)),
% 1.76/0.61    inference(backward_demodulation,[],[f140,f189])).
% 1.76/0.61  fof(f189,plain,(
% 1.76/0.61    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.76/0.61    inference(subsumption_resolution,[],[f188,f58])).
% 1.76/0.61  fof(f58,plain,(
% 1.76/0.61    k1_xboole_0 != sK1),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f188,plain,(
% 1.76/0.61    k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.76/0.61    inference(subsumption_resolution,[],[f187,f56])).
% 1.76/0.61  fof(f56,plain,(
% 1.76/0.61    v2_funct_1(sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f187,plain,(
% 1.76/0.61    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.76/0.61    inference(subsumption_resolution,[],[f186,f54])).
% 1.76/0.61  fof(f54,plain,(
% 1.76/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f186,plain,(
% 1.76/0.61    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.76/0.61    inference(subsumption_resolution,[],[f185,f62])).
% 1.76/0.61  fof(f185,plain,(
% 1.76/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.76/0.61    inference(subsumption_resolution,[],[f174,f60])).
% 1.76/0.61  fof(f174,plain,(
% 1.76/0.61    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.76/0.61    inference(resolution,[],[f61,f91])).
% 1.76/0.61  fof(f91,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  fof(f44,plain,(
% 1.76/0.61    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.61    inference(flattening,[],[f43])).
% 1.76/0.61  fof(f43,plain,(
% 1.76/0.61    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.61    inference(ennf_transformation,[],[f20])).
% 1.76/0.61  fof(f20,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.76/0.61  fof(f61,plain,(
% 1.76/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f140,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f130,f60])).
% 1.76/0.61  fof(f130,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))),
% 1.76/0.61    inference(resolution,[],[f56,f76])).
% 1.76/0.61  fof(f76,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f33])).
% 1.76/0.61  fof(f33,plain,(
% 1.76/0.61    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f32])).
% 1.76/0.61  fof(f32,plain,(
% 1.76/0.61    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f11])).
% 1.76/0.61  fof(f11,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 1.76/0.61  fof(f336,plain,(
% 1.76/0.61    ( ! [X1] : (sK0 != k1_relat_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))) )),
% 1.76/0.61    inference(subsumption_resolution,[],[f330,f261])).
% 1.76/0.61  fof(f330,plain,(
% 1.76/0.61    ( ! [X1] : (sK0 != k1_relat_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))) )),
% 1.76/0.61    inference(backward_demodulation,[],[f154,f326])).
% 1.76/0.61  fof(f326,plain,(
% 1.76/0.61    sK0 = k1_relat_1(sK2)),
% 1.76/0.61    inference(resolution,[],[f183,f261])).
% 1.76/0.61  fof(f183,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 1.76/0.61    inference(forward_demodulation,[],[f181,f97])).
% 1.76/0.61  fof(f181,plain,(
% 1.76/0.61    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2)),
% 1.76/0.61    inference(backward_demodulation,[],[f142,f179])).
% 1.76/0.61  fof(f179,plain,(
% 1.76/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f178,f58])).
% 1.76/0.61  fof(f178,plain,(
% 1.76/0.61    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f177,f56])).
% 1.76/0.61  fof(f177,plain,(
% 1.76/0.61    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f176,f54])).
% 1.76/0.61  fof(f176,plain,(
% 1.76/0.61    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f175,f62])).
% 1.76/0.61  fof(f175,plain,(
% 1.76/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f173,f60])).
% 1.76/0.61  fof(f173,plain,(
% 1.76/0.61    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(resolution,[],[f61,f90])).
% 1.76/0.61  fof(f90,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f44])).
% 1.76/0.61  fof(f142,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.76/0.61    inference(subsumption_resolution,[],[f132,f60])).
% 1.76/0.61  fof(f132,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.76/0.61    inference(resolution,[],[f56,f78])).
% 1.76/0.61  fof(f78,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f35])).
% 1.76/0.61  fof(f35,plain,(
% 1.76/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f34])).
% 1.76/0.61  fof(f34,plain,(
% 1.76/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f10])).
% 1.76/0.61  fof(f10,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 1.76/0.61  fof(f154,plain,(
% 1.76/0.61    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK2) | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))) )),
% 1.76/0.61    inference(resolution,[],[f60,f81])).
% 1.76/0.61  fof(f81,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f39])).
% 1.76/0.61  fof(f39,plain,(
% 1.76/0.61    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f38])).
% 1.76/0.61  fof(f38,plain,(
% 1.76/0.61    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f8])).
% 1.76/0.61  fof(f8,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 1.76/0.61  fof(f231,plain,(
% 1.76/0.61    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 1.76/0.61    inference(resolution,[],[f196,f100])).
% 1.76/0.61  fof(f100,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.76/0.61    inference(definition_unfolding,[],[f69,f63])).
% 1.76/0.61  fof(f69,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f26,plain,(
% 1.76/0.61    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.76/0.61    inference(ennf_transformation,[],[f5])).
% 1.76/0.61  fof(f5,axiom,(
% 1.76/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.76/0.61  fof(f1585,plain,(
% 1.76/0.61    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.76/0.61    inference(forward_demodulation,[],[f1479,f334])).
% 1.76/0.61  fof(f334,plain,(
% 1.76/0.61    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 1.76/0.61    inference(backward_demodulation,[],[f319,f333])).
% 1.76/0.61  fof(f333,plain,(
% 1.76/0.61    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f328,f261])).
% 1.76/0.61  fof(f328,plain,(
% 1.76/0.61    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.76/0.61    inference(backward_demodulation,[],[f138,f326])).
% 1.76/0.61  fof(f138,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.76/0.61    inference(subsumption_resolution,[],[f128,f60])).
% 1.76/0.61  fof(f128,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.76/0.61    inference(resolution,[],[f56,f74])).
% 1.76/0.61  fof(f74,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f31])).
% 1.76/0.61  fof(f31,plain,(
% 1.76/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f30])).
% 1.76/0.61  fof(f30,plain,(
% 1.76/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f9])).
% 1.76/0.61  fof(f9,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.76/0.61  fof(f319,plain,(
% 1.76/0.61    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))),
% 1.76/0.61    inference(resolution,[],[f282,f99])).
% 1.76/0.61  fof(f99,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.76/0.61    inference(definition_unfolding,[],[f68,f63])).
% 1.76/0.61  fof(f68,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f25])).
% 1.76/0.61  fof(f25,plain,(
% 1.76/0.61    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.76/0.61    inference(ennf_transformation,[],[f6])).
% 1.76/0.61  fof(f6,axiom,(
% 1.76/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.76/0.61  fof(f282,plain,(
% 1.76/0.61    v1_relat_1(k2_funct_1(sK2))),
% 1.76/0.61    inference(resolution,[],[f261,f145])).
% 1.76/0.61  fof(f145,plain,(
% 1.76/0.61    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 1.76/0.61    inference(resolution,[],[f60,f71])).
% 1.76/0.61  fof(f71,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f29])).
% 1.76/0.61  fof(f29,plain,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f28])).
% 1.76/0.61  fof(f28,plain,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f7])).
% 1.76/0.61  fof(f7,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.76/0.61  fof(f1479,plain,(
% 1.76/0.61    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.76/0.61    inference(backward_demodulation,[],[f711,f1448])).
% 1.76/0.61  fof(f711,plain,(
% 1.76/0.61    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.76/0.61    inference(resolution,[],[f705,f196])).
% 1.76/0.61  fof(f705,plain,(
% 1.76/0.61    ( ! [X7] : (~v1_relat_1(X7) | k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X7)) = k5_relat_1(k6_partfun1(sK1),X7)) )),
% 1.76/0.61    inference(forward_demodulation,[],[f702,f189])).
% 1.76/0.61  fof(f702,plain,(
% 1.76/0.61    ( ! [X7] : (~v1_relat_1(X7) | k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X7) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X7))) )),
% 1.76/0.61    inference(resolution,[],[f284,f282])).
% 1.76/0.61  fof(f284,plain,(
% 1.76/0.61    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3))) )),
% 1.76/0.61    inference(resolution,[],[f261,f70])).
% 1.76/0.61  fof(f70,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f27])).
% 1.76/0.61  fof(f27,plain,(
% 1.76/0.61    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(ennf_transformation,[],[f3])).
% 1.76/0.61  fof(f3,axiom,(
% 1.76/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.76/0.61  % SZS output end Proof for theBenchmark
% 1.76/0.61  % (22870)------------------------------
% 1.76/0.61  % (22870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.61  % (22870)Termination reason: Refutation
% 1.76/0.61  
% 1.76/0.61  % (22870)Memory used [KB]: 2430
% 1.76/0.61  % (22870)Time elapsed: 0.201 s
% 1.76/0.61  % (22870)------------------------------
% 1.76/0.61  % (22870)------------------------------
% 1.76/0.61  % (22852)Success in time 0.248 s
%------------------------------------------------------------------------------
