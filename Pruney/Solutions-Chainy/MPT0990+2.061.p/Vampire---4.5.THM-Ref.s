%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:38 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  197 (4562 expanded)
%              Number of leaves         :   20 ( 829 expanded)
%              Depth                    :   29
%              Number of atoms          :  636 (34307 expanded)
%              Number of equality atoms :  229 (10826 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1837,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1836,f55])).

fof(f55,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1836,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f331,f1815])).

fof(f1815,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f1733,f1757])).

fof(f1757,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f1715,f1748])).

fof(f1748,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f1708,f1722])).

fof(f1722,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f1719,f319])).

fof(f319,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f317,f300])).

fof(f300,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f282,f50])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f282,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f58,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f317,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f281,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f66,f61])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f281,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1719,plain,(
    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f1165,f1715])).

fof(f1165,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f515,f1136])).

fof(f1136,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1135,f728])).

fof(f728,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f725,f722])).

fof(f722,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f717,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f717,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f248,f58])).

fof(f248,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X6)
      | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3) ) ),
    inference(subsumption_resolution,[],[f230,f47])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f230,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3) ) ),
    inference(resolution,[],[f49,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f725,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f335,f722])).

fof(f335,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f333,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f333,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f51,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f1135,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1134,f49])).

fof(f1134,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1133,f47])).

fof(f1133,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1132,f58])).

fof(f1132,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1131,f56])).

fof(f1131,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f88,f722])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f515,plain,(
    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f511,f251])).

fof(f251,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f223,f106])).

fof(f106,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f47,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f223,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f49,f75])).

fof(f511,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(sK2,sK3),X8) = k5_relat_1(sK2,k5_relat_1(sK3,X8)) ) ),
    inference(resolution,[],[f253,f281])).

fof(f253,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f223,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1708,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f1481,f1698])).

fof(f1698,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1697,f1173])).

fof(f1173,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f726,f1136])).

fof(f726,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f51,f722])).

fof(f1697,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1696,f1171])).

fof(f1171,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f722,f1136])).

fof(f1696,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1695,f58])).

fof(f1695,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1694,f56])).

fof(f1694,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(resolution,[],[f246,f57])).

fof(f57,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f246,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0)
      | sK0 = k2_relat_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) ) ),
    inference(backward_demodulation,[],[f173,f224])).

fof(f224,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f49,f76])).

fof(f173,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f172,f49])).

fof(f172,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(resolution,[],[f48,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f1481,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f273,f1480])).

fof(f1480,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1479,f47])).

fof(f1479,plain,
    ( ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1473,f223])).

fof(f1473,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f1466,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1466,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1465,f91])).

fof(f91,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1465,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f1464,f1171])).

fof(f1464,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1463,f90])).

fof(f90,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f59,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f53,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f1463,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | o_0_0_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1462,f49])).

fof(f1462,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | o_0_0_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1461,f47])).

fof(f1461,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | o_0_0_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f218,f48])).

fof(f218,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X2,sK1,X3)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | o_0_0_xboole_0 = X3
      | v2_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f217,f50])).

fof(f217,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | o_0_0_xboole_0 = X3
      | v2_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f216,f58])).

fof(f216,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | o_0_0_xboole_0 = X3
      | v2_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f196,f56])).

fof(f196,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | o_0_0_xboole_0 = X3
      | v2_funct_1(X2) ) ),
    inference(resolution,[],[f57,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k2_relset_1(X0,X1,X3) != X1
      | o_0_0_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(definition_unfolding,[],[f83,f59])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f273,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) ),
    inference(resolution,[],[f251,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f67,f61])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1715,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1712,f1466])).

fof(f1712,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f1702])).

fof(f1702,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f244,f1698])).

fof(f244,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f181,f224])).

fof(f181,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f180,f90])).

fof(f180,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f179,f49])).

fof(f179,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f167,f47])).

fof(f167,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(resolution,[],[f48,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | o_0_0_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(definition_unfolding,[],[f77,f59])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f1733,plain,(
    sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f398,f1730])).

fof(f1730,plain,(
    sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f1727,f1729])).

fof(f1729,plain,(
    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f1711,f1466])).

fof(f1711,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(trivial_inequality_removal,[],[f1703])).

fof(f1703,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(backward_demodulation,[],[f245,f1698])).

fof(f245,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(backward_demodulation,[],[f178,f224])).

fof(f178,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f177,f90])).

fof(f177,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = sK0
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f176,f49])).

fof(f176,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = sK0
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f166,f47])).

fof(f166,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | o_0_0_xboole_0 = sK0
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(resolution,[],[f48,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | o_0_0_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(definition_unfolding,[],[f78,f59])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1727,plain,(
    sK3 = k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) ),
    inference(backward_demodulation,[],[f1718,f1726])).

fof(f1726,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(backward_demodulation,[],[f262,f1723])).

fof(f1723,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1720,f93])).

fof(f93,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f61])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1720,plain,(
    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) ),
    inference(backward_demodulation,[],[f1476,f1715])).

fof(f1476,plain,(
    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(subsumption_resolution,[],[f1475,f47])).

fof(f1475,plain,
    ( ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(subsumption_resolution,[],[f1471,f223])).

fof(f1471,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f1466,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f262,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f223,f95])).

fof(f1718,plain,(
    k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(backward_demodulation,[],[f580,f1715])).

fof(f580,plain,(
    k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK3) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) ),
    inference(resolution,[],[f561,f251])).

fof(f561,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(sK3,X9),sK3) = k5_relat_1(sK3,k5_relat_1(X9,sK3)) ) ),
    inference(resolution,[],[f254,f223])).

fof(f254,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),sK3) = k5_relat_1(X4,k5_relat_1(X5,sK3)) ) ),
    inference(resolution,[],[f223,f68])).

fof(f398,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f395,f211])).

fof(f211,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f210,f89])).

fof(f89,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f210,plain,
    ( o_0_0_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f209,f52])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f209,plain,
    ( ~ v2_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f208,f50])).

fof(f208,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f207,f58])).

fof(f207,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f195,f56])).

fof(f195,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f57,f97])).

fof(f395,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(resolution,[],[f390,f307])).

fof(f307,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f281,f140])).

fof(f140,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f56,f69])).

fof(f390,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(sK3,sK2),X8) = k5_relat_1(sK3,k5_relat_1(sK2,X8)) ) ),
    inference(resolution,[],[f252,f281])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f223,f68])).

fof(f331,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f330,f302])).

fof(f302,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f301,f281])).

fof(f301,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f138,f300])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f134,f56])).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f52,f71])).

fof(f330,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) ),
    inference(resolution,[],[f307,f95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (4307)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (4323)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (4314)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (4315)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (4305)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (4308)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.56  % (4320)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.56  % (4322)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.27/0.56  % (4332)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.56  % (4325)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.56  % (4312)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.27/0.57  % (4303)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.57  % (4324)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.55/0.57  % (4328)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.55/0.57  % (4318)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.57  % (4310)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.57  % (4304)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.55/0.57  % (4326)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.57  % (4313)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.58  % (4330)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.58  % (4317)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.58  % (4329)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.58  % (4316)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.55/0.59  % (4331)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.59  % (4311)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.55/0.59  % (4309)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.59  % (4306)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.59  % (4327)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.55/0.60  % (4319)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.60  % (4319)Refutation not found, incomplete strategy% (4319)------------------------------
% 1.55/0.60  % (4319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (4319)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (4319)Memory used [KB]: 10746
% 1.55/0.60  % (4319)Time elapsed: 0.176 s
% 1.55/0.60  % (4319)------------------------------
% 1.55/0.60  % (4319)------------------------------
% 1.55/0.61  % (4321)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.64  % (4320)Refutation found. Thanks to Tanya!
% 1.55/0.64  % SZS status Theorem for theBenchmark
% 2.12/0.65  % SZS output start Proof for theBenchmark
% 2.12/0.65  fof(f1837,plain,(
% 2.12/0.65    $false),
% 2.12/0.65    inference(subsumption_resolution,[],[f1836,f55])).
% 2.12/0.65  fof(f55,plain,(
% 2.12/0.65    sK3 != k2_funct_1(sK2)),
% 2.12/0.65    inference(cnf_transformation,[],[f23])).
% 2.12/0.65  fof(f23,plain,(
% 2.12/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.12/0.65    inference(flattening,[],[f22])).
% 2.12/0.65  fof(f22,plain,(
% 2.12/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.12/0.65    inference(ennf_transformation,[],[f21])).
% 2.12/0.65  fof(f21,negated_conjecture,(
% 2.12/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.12/0.65    inference(negated_conjecture,[],[f20])).
% 2.12/0.65  fof(f20,conjecture,(
% 2.12/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.12/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.12/0.65  fof(f1836,plain,(
% 2.12/0.65    sK3 = k2_funct_1(sK2)),
% 2.12/0.65    inference(backward_demodulation,[],[f331,f1815])).
% 2.12/0.65  fof(f1815,plain,(
% 2.12/0.65    sK3 = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))),
% 2.12/0.65    inference(backward_demodulation,[],[f1733,f1757])).
% 2.12/0.65  fof(f1757,plain,(
% 2.12/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 2.12/0.65    inference(backward_demodulation,[],[f1715,f1748])).
% 2.12/0.65  fof(f1748,plain,(
% 2.12/0.65    sK2 = k2_funct_1(sK3)),
% 2.12/0.65    inference(forward_demodulation,[],[f1708,f1722])).
% 2.12/0.65  fof(f1722,plain,(
% 2.12/0.65    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.12/0.65    inference(forward_demodulation,[],[f1719,f319])).
% 2.12/0.65  fof(f319,plain,(
% 2.12/0.65    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.12/0.65    inference(forward_demodulation,[],[f317,f300])).
% 2.12/0.65  fof(f300,plain,(
% 2.12/0.65    sK1 = k2_relat_1(sK2)),
% 2.12/0.65    inference(forward_demodulation,[],[f282,f50])).
% 2.12/0.65  fof(f50,plain,(
% 2.12/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.12/0.65    inference(cnf_transformation,[],[f23])).
% 2.12/0.65  fof(f282,plain,(
% 2.12/0.65    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.12/0.65    inference(resolution,[],[f58,f76])).
% 2.12/0.65  fof(f76,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f34])).
% 2.12/0.65  fof(f34,plain,(
% 2.12/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/0.65    inference(ennf_transformation,[],[f11])).
% 2.12/0.65  fof(f11,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.12/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.12/0.65  fof(f58,plain,(
% 2.12/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.12/0.65    inference(cnf_transformation,[],[f23])).
% 2.12/0.65  fof(f317,plain,(
% 2.12/0.65    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 2.12/0.65    inference(resolution,[],[f281,f94])).
% 2.12/0.65  fof(f94,plain,(
% 2.12/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.12/0.65    inference(definition_unfolding,[],[f66,f61])).
% 2.12/0.65  fof(f61,plain,(
% 2.12/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f16])).
% 2.12/0.65  fof(f16,axiom,(
% 2.12/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.12/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.12/0.65  fof(f66,plain,(
% 2.12/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.12/0.65    inference(cnf_transformation,[],[f24])).
% 2.12/0.65  fof(f24,plain,(
% 2.12/0.65    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.12/0.65    inference(ennf_transformation,[],[f5])).
% 2.12/0.65  fof(f5,axiom,(
% 2.12/0.65    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.12/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.12/0.65  fof(f281,plain,(
% 2.12/0.65    v1_relat_1(sK2)),
% 2.12/0.65    inference(resolution,[],[f58,f75])).
% 2.12/0.65  fof(f75,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f33])).
% 2.12/0.65  fof(f33,plain,(
% 2.12/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/0.65    inference(ennf_transformation,[],[f10])).
% 2.12/0.65  fof(f10,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.12/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.12/0.65  fof(f1719,plain,(
% 2.12/0.65    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.12/0.65    inference(backward_demodulation,[],[f1165,f1715])).
% 2.12/0.65  fof(f1165,plain,(
% 2.12/0.65    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.12/0.65    inference(backward_demodulation,[],[f515,f1136])).
% 2.12/0.65  fof(f1136,plain,(
% 2.12/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.12/0.65    inference(resolution,[],[f1135,f728])).
% 2.12/0.65  fof(f728,plain,(
% 2.12/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.12/0.65    inference(forward_demodulation,[],[f725,f722])).
% 2.12/0.65  fof(f722,plain,(
% 2.12/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.12/0.65    inference(subsumption_resolution,[],[f717,f56])).
% 2.12/0.65  fof(f56,plain,(
% 2.12/0.65    v1_funct_1(sK2)),
% 2.12/0.65    inference(cnf_transformation,[],[f23])).
% 2.12/0.65  fof(f717,plain,(
% 2.12/0.65    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.12/0.65    inference(resolution,[],[f248,f58])).
% 2.12/0.65  fof(f248,plain,(
% 2.12/0.65    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X6) | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f230,f47])).
% 2.12/0.65  fof(f47,plain,(
% 2.12/0.65    v1_funct_1(sK3)),
% 2.12/0.65    inference(cnf_transformation,[],[f23])).
% 2.12/0.65  fof(f230,plain,(
% 2.12/0.65    ( ! [X6,X8,X7] : (~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(sK3) | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3)) )),
% 2.12/0.65    inference(resolution,[],[f49,f86])).
% 2.12/0.65  fof(f86,plain,(
% 2.12/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f44])).
% 2.12/0.65  fof(f44,plain,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.12/0.65    inference(flattening,[],[f43])).
% 2.12/0.65  fof(f43,plain,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.12/0.65    inference(ennf_transformation,[],[f15])).
% 2.12/0.65  fof(f15,axiom,(
% 2.12/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.12/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.12/0.65  fof(f49,plain,(
% 2.12/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.12/0.65    inference(cnf_transformation,[],[f23])).
% 2.12/0.65  fof(f725,plain,(
% 2.12/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.12/0.65    inference(backward_demodulation,[],[f335,f722])).
% 2.12/0.65  fof(f335,plain,(
% 2.12/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.12/0.65    inference(subsumption_resolution,[],[f333,f63])).
% 2.12/0.65  fof(f63,plain,(
% 2.12/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f14])).
% 2.12/0.66  fof(f14,axiom,(
% 2.12/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.12/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.12/0.66  fof(f333,plain,(
% 2.12/0.66    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.12/0.66    inference(resolution,[],[f51,f85])).
% 2.12/0.66  fof(f85,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f42])).
% 2.12/0.67  fof(f42,plain,(
% 2.12/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/0.67    inference(flattening,[],[f41])).
% 2.12/0.67  fof(f41,plain,(
% 2.12/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.12/0.67    inference(ennf_transformation,[],[f12])).
% 2.12/0.67  fof(f12,axiom,(
% 2.12/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.12/0.67  fof(f51,plain,(
% 2.12/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.12/0.67    inference(cnf_transformation,[],[f23])).
% 2.12/0.67  fof(f1135,plain,(
% 2.12/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1134,f49])).
% 2.12/0.67  fof(f1134,plain,(
% 2.12/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1133,f47])).
% 2.12/0.67  fof(f1133,plain,(
% 2.12/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1132,f58])).
% 2.12/0.67  fof(f1132,plain,(
% 2.12/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1131,f56])).
% 2.12/0.67  fof(f1131,plain,(
% 2.12/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.12/0.67    inference(superposition,[],[f88,f722])).
% 2.12/0.67  fof(f88,plain,(
% 2.12/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f46])).
% 2.12/0.67  fof(f46,plain,(
% 2.12/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.12/0.67    inference(flattening,[],[f45])).
% 2.12/0.67  fof(f45,plain,(
% 2.12/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.12/0.67    inference(ennf_transformation,[],[f13])).
% 2.12/0.67  fof(f13,axiom,(
% 2.12/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.12/0.67  fof(f515,plain,(
% 2.12/0.67    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.12/0.67    inference(resolution,[],[f511,f251])).
% 2.12/0.67  fof(f251,plain,(
% 2.12/0.67    v1_relat_1(k2_funct_1(sK3))),
% 2.12/0.67    inference(resolution,[],[f223,f106])).
% 2.12/0.67  fof(f106,plain,(
% 2.12/0.67    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 2.12/0.67    inference(resolution,[],[f47,f69])).
% 2.12/0.67  fof(f69,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f28])).
% 2.12/0.67  fof(f28,plain,(
% 2.12/0.67    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.67    inference(flattening,[],[f27])).
% 2.12/0.67  fof(f27,plain,(
% 2.12/0.67    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.12/0.67    inference(ennf_transformation,[],[f6])).
% 2.12/0.67  fof(f6,axiom,(
% 2.12/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.12/0.67  fof(f223,plain,(
% 2.12/0.67    v1_relat_1(sK3)),
% 2.12/0.67    inference(resolution,[],[f49,f75])).
% 2.12/0.67  fof(f511,plain,(
% 2.12/0.67    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(k5_relat_1(sK2,sK3),X8) = k5_relat_1(sK2,k5_relat_1(sK3,X8))) )),
% 2.12/0.67    inference(resolution,[],[f253,f281])).
% 2.12/0.67  fof(f253,plain,(
% 2.12/0.67    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3))) )),
% 2.12/0.67    inference(resolution,[],[f223,f68])).
% 2.12/0.67  fof(f68,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f26])).
% 2.12/0.67  fof(f26,plain,(
% 2.12/0.67    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.12/0.67    inference(ennf_transformation,[],[f2])).
% 2.12/0.67  fof(f2,axiom,(
% 2.12/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.12/0.67  fof(f1708,plain,(
% 2.12/0.67    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.12/0.67    inference(backward_demodulation,[],[f1481,f1698])).
% 2.12/0.67  fof(f1698,plain,(
% 2.12/0.67    sK0 = k2_relat_1(sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f1697,f1173])).
% 2.12/0.67  fof(f1173,plain,(
% 2.12/0.67    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 2.12/0.67    inference(backward_demodulation,[],[f726,f1136])).
% 2.12/0.67  fof(f726,plain,(
% 2.12/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.12/0.67    inference(backward_demodulation,[],[f51,f722])).
% 2.12/0.67  fof(f1697,plain,(
% 2.12/0.67    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relat_1(sK3)),
% 2.12/0.67    inference(forward_demodulation,[],[f1696,f1171])).
% 2.12/0.67  fof(f1171,plain,(
% 2.12/0.67    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.12/0.67    inference(backward_demodulation,[],[f722,f1136])).
% 2.12/0.67  fof(f1696,plain,(
% 2.12/0.67    sK0 = k2_relat_1(sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1695,f58])).
% 2.12/0.67  fof(f1695,plain,(
% 2.12/0.67    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1694,f56])).
% 2.12/0.67  fof(f1694,plain,(
% 2.12/0.67    ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.12/0.67    inference(resolution,[],[f246,f57])).
% 2.12/0.67  fof(f57,plain,(
% 2.12/0.67    v1_funct_2(sK2,sK0,sK1)),
% 2.12/0.67    inference(cnf_transformation,[],[f23])).
% 2.12/0.67  fof(f246,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))) )),
% 2.12/0.67    inference(backward_demodulation,[],[f173,f224])).
% 2.12/0.67  fof(f224,plain,(
% 2.12/0.67    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.12/0.67    inference(resolution,[],[f49,f76])).
% 2.12/0.67  fof(f173,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.12/0.67    inference(subsumption_resolution,[],[f172,f49])).
% 2.12/0.67  fof(f172,plain,(
% 2.12/0.67    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.12/0.67    inference(subsumption_resolution,[],[f164,f47])).
% 2.12/0.67  fof(f164,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.12/0.67    inference(resolution,[],[f48,f79])).
% 2.12/0.67  fof(f79,plain,(
% 2.12/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.12/0.67    inference(cnf_transformation,[],[f38])).
% 2.12/0.67  fof(f38,plain,(
% 2.12/0.67    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.12/0.67    inference(flattening,[],[f37])).
% 2.12/0.67  fof(f37,plain,(
% 2.12/0.67    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.12/0.67    inference(ennf_transformation,[],[f17])).
% 2.12/0.67  fof(f17,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.12/0.67  fof(f48,plain,(
% 2.12/0.67    v1_funct_2(sK3,sK1,sK0)),
% 2.12/0.67    inference(cnf_transformation,[],[f23])).
% 2.12/0.67  fof(f1481,plain,(
% 2.12/0.67    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3))),
% 2.12/0.67    inference(backward_demodulation,[],[f273,f1480])).
% 2.12/0.67  fof(f1480,plain,(
% 2.12/0.67    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1479,f47])).
% 2.12/0.67  fof(f1479,plain,(
% 2.12/0.67    ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1473,f223])).
% 2.12/0.67  fof(f1473,plain,(
% 2.12/0.67    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.12/0.67    inference(resolution,[],[f1466,f71])).
% 2.12/0.67  fof(f71,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f30])).
% 2.12/0.67  fof(f30,plain,(
% 2.12/0.67    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.67    inference(flattening,[],[f29])).
% 2.12/0.67  fof(f29,plain,(
% 2.12/0.67    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.12/0.67    inference(ennf_transformation,[],[f8])).
% 2.12/0.67  fof(f8,axiom,(
% 2.12/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.12/0.67  fof(f1466,plain,(
% 2.12/0.67    v2_funct_1(sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f1465,f91])).
% 2.12/0.67  fof(f91,plain,(
% 2.12/0.67    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.12/0.67    inference(definition_unfolding,[],[f60,f61])).
% 2.12/0.67  fof(f60,plain,(
% 2.12/0.67    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f7])).
% 2.12/0.67  fof(f7,axiom,(
% 2.12/0.67    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 2.12/0.67  fof(f1465,plain,(
% 2.12/0.67    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3)),
% 2.12/0.67    inference(forward_demodulation,[],[f1464,f1171])).
% 2.12/0.67  fof(f1464,plain,(
% 2.12/0.67    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f1463,f90])).
% 2.12/0.67  fof(f90,plain,(
% 2.12/0.67    o_0_0_xboole_0 != sK0),
% 2.12/0.67    inference(definition_unfolding,[],[f53,f59])).
% 2.12/0.67  fof(f59,plain,(
% 2.12/0.67    k1_xboole_0 = o_0_0_xboole_0),
% 2.12/0.67    inference(cnf_transformation,[],[f1])).
% 2.12/0.67  fof(f1,axiom,(
% 2.12/0.67    k1_xboole_0 = o_0_0_xboole_0),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 2.12/0.67  fof(f53,plain,(
% 2.12/0.67    k1_xboole_0 != sK0),
% 2.12/0.67    inference(cnf_transformation,[],[f23])).
% 2.12/0.67  fof(f1463,plain,(
% 2.12/0.67    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | o_0_0_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f1462,f49])).
% 2.12/0.67  fof(f1462,plain,(
% 2.12/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | o_0_0_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f1461,f47])).
% 2.12/0.67  fof(f1461,plain,(
% 2.12/0.67    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | o_0_0_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.12/0.67    inference(resolution,[],[f218,f48])).
% 2.12/0.67  fof(f218,plain,(
% 2.12/0.67    ( ! [X2,X3] : (~v1_funct_2(X2,sK1,X3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | o_0_0_xboole_0 = X3 | v2_funct_1(X2)) )),
% 2.12/0.67    inference(subsumption_resolution,[],[f217,f50])).
% 2.12/0.67  fof(f217,plain,(
% 2.12/0.67    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_funct_2(X2,sK1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | sK1 != k2_relset_1(sK0,sK1,sK2) | o_0_0_xboole_0 = X3 | v2_funct_1(X2)) )),
% 2.12/0.67    inference(subsumption_resolution,[],[f216,f58])).
% 2.12/0.67  fof(f216,plain,(
% 2.12/0.67    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | sK1 != k2_relset_1(sK0,sK1,sK2) | o_0_0_xboole_0 = X3 | v2_funct_1(X2)) )),
% 2.12/0.67    inference(subsumption_resolution,[],[f196,f56])).
% 2.12/0.67  fof(f196,plain,(
% 2.12/0.67    ( ! [X2,X3] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X3,sK2,X2)) | sK1 != k2_relset_1(sK0,sK1,sK2) | o_0_0_xboole_0 = X3 | v2_funct_1(X2)) )),
% 2.12/0.67    inference(resolution,[],[f57,f98])).
% 2.12/0.67  fof(f98,plain,(
% 2.12/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | o_0_0_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.12/0.67    inference(definition_unfolding,[],[f83,f59])).
% 2.12/0.67  fof(f83,plain,(
% 2.12/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f40])).
% 2.12/0.67  fof(f40,plain,(
% 2.12/0.67    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.12/0.67    inference(flattening,[],[f39])).
% 2.12/0.67  fof(f39,plain,(
% 2.12/0.67    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.12/0.67    inference(ennf_transformation,[],[f18])).
% 2.12/0.67  fof(f18,axiom,(
% 2.12/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.12/0.67  fof(f273,plain,(
% 2.12/0.67    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))),
% 2.12/0.67    inference(resolution,[],[f251,f95])).
% 2.12/0.67  fof(f95,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.12/0.67    inference(definition_unfolding,[],[f67,f61])).
% 2.12/0.67  fof(f67,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.12/0.67    inference(cnf_transformation,[],[f25])).
% 2.12/0.67  fof(f25,plain,(
% 2.12/0.67    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.12/0.67    inference(ennf_transformation,[],[f4])).
% 2.12/0.67  fof(f4,axiom,(
% 2.12/0.67    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.12/0.67  fof(f1715,plain,(
% 2.12/0.67    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1712,f1466])).
% 2.12/0.67  fof(f1712,plain,(
% 2.12/0.67    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(trivial_inequality_removal,[],[f1702])).
% 2.12/0.67  fof(f1702,plain,(
% 2.12/0.67    sK0 != sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(backward_demodulation,[],[f244,f1698])).
% 2.12/0.67  fof(f244,plain,(
% 2.12/0.67    ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(backward_demodulation,[],[f181,f224])).
% 2.12/0.67  fof(f181,plain,(
% 2.12/0.67    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(subsumption_resolution,[],[f180,f90])).
% 2.12/0.67  fof(f180,plain,(
% 2.12/0.67    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(subsumption_resolution,[],[f179,f49])).
% 2.12/0.67  fof(f179,plain,(
% 2.12/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(subsumption_resolution,[],[f167,f47])).
% 2.12/0.67  fof(f167,plain,(
% 2.12/0.67    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.12/0.67    inference(resolution,[],[f48,f97])).
% 2.12/0.67  fof(f97,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | o_0_0_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.12/0.67    inference(definition_unfolding,[],[f77,f59])).
% 2.12/0.67  fof(f77,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f36])).
% 2.12/0.67  fof(f36,plain,(
% 2.12/0.67    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.12/0.67    inference(flattening,[],[f35])).
% 2.12/0.67  fof(f35,plain,(
% 2.12/0.67    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.12/0.67    inference(ennf_transformation,[],[f19])).
% 2.12/0.67  fof(f19,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.12/0.67  fof(f1733,plain,(
% 2.12/0.67    sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2))),
% 2.12/0.67    inference(backward_demodulation,[],[f398,f1730])).
% 2.12/0.67  fof(f1730,plain,(
% 2.12/0.67    sK3 = k5_relat_1(sK3,k6_partfun1(sK0))),
% 2.12/0.67    inference(backward_demodulation,[],[f1727,f1729])).
% 2.12/0.67  fof(f1729,plain,(
% 2.12/0.67    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f1711,f1466])).
% 2.12/0.67  fof(f1711,plain,(
% 2.12/0.67    ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(trivial_inequality_removal,[],[f1703])).
% 2.12/0.67  fof(f1703,plain,(
% 2.12/0.67    sK0 != sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(backward_demodulation,[],[f245,f1698])).
% 2.12/0.67  fof(f245,plain,(
% 2.12/0.67    ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(backward_demodulation,[],[f178,f224])).
% 2.12/0.67  fof(f178,plain,(
% 2.12/0.67    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f177,f90])).
% 2.12/0.67  fof(f177,plain,(
% 2.12/0.67    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = sK0 | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f176,f49])).
% 2.12/0.67  fof(f176,plain,(
% 2.12/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = sK0 | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(subsumption_resolution,[],[f166,f47])).
% 2.12/0.67  fof(f166,plain,(
% 2.12/0.67    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | o_0_0_xboole_0 = sK0 | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 2.12/0.67    inference(resolution,[],[f48,f96])).
% 2.12/0.67  fof(f96,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | o_0_0_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 2.12/0.67    inference(definition_unfolding,[],[f78,f59])).
% 2.12/0.67  fof(f78,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f36])).
% 2.12/0.67  fof(f1727,plain,(
% 2.12/0.67    sK3 = k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3))),
% 2.12/0.67    inference(backward_demodulation,[],[f1718,f1726])).
% 2.12/0.67  fof(f1726,plain,(
% 2.12/0.67    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.12/0.67    inference(backward_demodulation,[],[f262,f1723])).
% 2.12/0.67  fof(f1723,plain,(
% 2.12/0.67    sK1 = k1_relat_1(sK3)),
% 2.12/0.67    inference(forward_demodulation,[],[f1720,f93])).
% 2.12/0.67  fof(f93,plain,(
% 2.12/0.67    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.12/0.67    inference(definition_unfolding,[],[f64,f61])).
% 2.12/0.67  fof(f64,plain,(
% 2.12/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.12/0.67    inference(cnf_transformation,[],[f3])).
% 2.12/0.67  fof(f3,axiom,(
% 2.12/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.12/0.67  fof(f1720,plain,(
% 2.12/0.67    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))),
% 2.12/0.67    inference(backward_demodulation,[],[f1476,f1715])).
% 2.12/0.67  fof(f1476,plain,(
% 2.12/0.67    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1475,f47])).
% 2.12/0.67  fof(f1475,plain,(
% 2.12/0.67    ~v1_funct_1(sK3) | k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.12/0.67    inference(subsumption_resolution,[],[f1471,f223])).
% 2.12/0.67  fof(f1471,plain,(
% 2.12/0.67    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.12/0.67    inference(resolution,[],[f1466,f73])).
% 2.12/0.67  fof(f73,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f32])).
% 2.12/0.67  fof(f32,plain,(
% 2.12/0.67    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.67    inference(flattening,[],[f31])).
% 2.12/0.67  fof(f31,plain,(
% 2.12/0.67    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.12/0.67    inference(ennf_transformation,[],[f9])).
% 2.12/0.67  fof(f9,axiom,(
% 2.12/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.12/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 2.12/0.67  fof(f262,plain,(
% 2.12/0.67    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 2.12/0.67    inference(resolution,[],[f223,f95])).
% 2.12/0.67  fof(f1718,plain,(
% 2.12/0.67    k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.12/0.67    inference(backward_demodulation,[],[f580,f1715])).
% 2.12/0.67  fof(f580,plain,(
% 2.12/0.67    k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK3) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3))),
% 2.12/0.67    inference(resolution,[],[f561,f251])).
% 2.12/0.67  fof(f561,plain,(
% 2.12/0.67    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(sK3,X9),sK3) = k5_relat_1(sK3,k5_relat_1(X9,sK3))) )),
% 2.12/0.67    inference(resolution,[],[f254,f223])).
% 2.12/0.67  fof(f254,plain,(
% 2.12/0.67    ( ! [X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,X5),sK3) = k5_relat_1(X4,k5_relat_1(X5,sK3))) )),
% 2.12/0.67    inference(resolution,[],[f223,f68])).
% 2.12/0.67  fof(f398,plain,(
% 2.12/0.67    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0))),
% 2.12/0.67    inference(forward_demodulation,[],[f395,f211])).
% 2.12/0.67  fof(f211,plain,(
% 2.12/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.12/0.67    inference(subsumption_resolution,[],[f210,f89])).
% 2.12/0.67  fof(f89,plain,(
% 2.12/0.67    o_0_0_xboole_0 != sK1),
% 2.12/0.67    inference(definition_unfolding,[],[f54,f59])).
% 2.12/0.67  fof(f54,plain,(
% 2.12/0.67    k1_xboole_0 != sK1),
% 2.12/0.67    inference(cnf_transformation,[],[f23])).
% 2.12/0.67  fof(f210,plain,(
% 2.12/0.67    o_0_0_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.12/0.67    inference(subsumption_resolution,[],[f209,f52])).
% 2.12/0.67  fof(f52,plain,(
% 2.12/0.67    v2_funct_1(sK2)),
% 2.12/0.67    inference(cnf_transformation,[],[f23])).
% 2.12/0.67  fof(f209,plain,(
% 2.12/0.67    ~v2_funct_1(sK2) | o_0_0_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.12/0.67    inference(subsumption_resolution,[],[f208,f50])).
% 2.12/0.67  fof(f208,plain,(
% 2.12/0.67    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | o_0_0_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.12/0.67    inference(subsumption_resolution,[],[f207,f58])).
% 2.12/0.67  fof(f207,plain,(
% 2.12/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | o_0_0_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.12/0.67    inference(subsumption_resolution,[],[f195,f56])).
% 2.12/0.67  fof(f195,plain,(
% 2.12/0.67    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | o_0_0_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.12/0.67    inference(resolution,[],[f57,f97])).
% 2.12/0.67  fof(f395,plain,(
% 2.12/0.67    k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2)))),
% 2.12/0.67    inference(resolution,[],[f390,f307])).
% 2.12/0.67  fof(f307,plain,(
% 2.12/0.67    v1_relat_1(k2_funct_1(sK2))),
% 2.12/0.67    inference(resolution,[],[f281,f140])).
% 2.12/0.67  fof(f140,plain,(
% 2.12/0.67    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 2.12/0.67    inference(resolution,[],[f56,f69])).
% 2.12/0.67  fof(f390,plain,(
% 2.12/0.67    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(k5_relat_1(sK3,sK2),X8) = k5_relat_1(sK3,k5_relat_1(sK2,X8))) )),
% 2.12/0.67    inference(resolution,[],[f252,f281])).
% 2.12/0.67  fof(f252,plain,(
% 2.12/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1))) )),
% 2.12/0.67    inference(resolution,[],[f223,f68])).
% 2.12/0.67  fof(f331,plain,(
% 2.12/0.67    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))),
% 2.12/0.67    inference(forward_demodulation,[],[f330,f302])).
% 2.12/0.67  fof(f302,plain,(
% 2.12/0.67    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.12/0.67    inference(subsumption_resolution,[],[f301,f281])).
% 2.12/0.67  fof(f301,plain,(
% 2.12/0.67    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.12/0.67    inference(backward_demodulation,[],[f138,f300])).
% 2.12/0.67  fof(f138,plain,(
% 2.12/0.67    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.12/0.67    inference(subsumption_resolution,[],[f134,f56])).
% 2.12/0.67  fof(f134,plain,(
% 2.12/0.67    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 2.12/0.67    inference(resolution,[],[f52,f71])).
% 2.12/0.67  fof(f330,plain,(
% 2.12/0.67    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2))),
% 2.12/0.67    inference(resolution,[],[f307,f95])).
% 2.12/0.67  % SZS output end Proof for theBenchmark
% 2.12/0.67  % (4320)------------------------------
% 2.12/0.67  % (4320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (4320)Termination reason: Refutation
% 2.12/0.67  
% 2.12/0.67  % (4320)Memory used [KB]: 2430
% 2.12/0.67  % (4320)Time elapsed: 0.228 s
% 2.12/0.67  % (4320)------------------------------
% 2.12/0.67  % (4320)------------------------------
% 2.12/0.67  % (4302)Success in time 0.3 s
%------------------------------------------------------------------------------
