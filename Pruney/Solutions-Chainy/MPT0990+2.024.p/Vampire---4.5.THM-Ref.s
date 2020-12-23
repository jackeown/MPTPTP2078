%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:32 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 366 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  348 (2217 expanded)
%              Number of equality atoms :   95 ( 695 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2321,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2320,f49])).

fof(f49,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f2320,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f2317,f202])).

fof(f202,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f201,f166])).

fof(f166,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f201,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f168,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f168,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2317,plain,(
    sK3 = k2_funct_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f2257,f434])).

fof(f434,plain,(
    ! [X0] : k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(k7_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f433,f200])).

fof(f200,plain,(
    ! [X8] : k7_relat_1(sK2,X8) = k5_relat_1(k6_partfun1(X8),sK2) ),
    inference(resolution,[],[f166,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f66,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f433,plain,(
    ! [X0] : k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f432,f77])).

fof(f77,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f53,f53])).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(f432,plain,(
    ! [X0] : k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0))) ),
    inference(subsumption_resolution,[],[f431,f82])).

fof(f82,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f53])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f431,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_partfun1(X0))
      | k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0))) ) ),
    inference(subsumption_resolution,[],[f430,f166])).

fof(f430,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(k6_partfun1(X0))
      | k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0))) ) ),
    inference(subsumption_resolution,[],[f427,f81])).

fof(f81,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f59,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f427,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(k6_partfun1(X0))
      | k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0))) ) ),
    inference(resolution,[],[f104,f79])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f53])).

fof(f57,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f104,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k5_relat_1(X0,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k5_relat_1(X0,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X0)) ) ),
    inference(resolution,[],[f46,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
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
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f2257,plain,(
    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f2256,f151])).

fof(f151,plain,(
    sK3 = k7_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f150,f121])).

fof(f121,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f43,f68])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f150,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK1) ),
    inference(resolution,[],[f123,f67])).

fof(f123,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f43,f70])).

fof(f2256,plain,(
    k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f2255,f965])).

fof(f965,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f964,f612])).

fof(f612,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f609,f606])).

fof(f606,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f596,f50])).

fof(f596,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f135,f52])).

fof(f135,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f128,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f128,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(resolution,[],[f43,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f609,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f188,f606])).

fof(f188,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f186,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f186,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f45,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f964,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f963,f43])).

fof(f963,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f962,f41])).

fof(f962,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f961,f52])).

fof(f961,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f960,f50])).

fof(f960,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f76,f606])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f2255,plain,(
    k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f2065,f149])).

fof(f149,plain,(
    ! [X8] : k7_relat_1(sK3,X8) = k5_relat_1(k6_partfun1(X8),sK3) ),
    inference(resolution,[],[f121,f85])).

fof(f2065,plain,(
    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(resolution,[],[f1811,f121])).

fof(f1811,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X26)) = k5_relat_1(k6_partfun1(sK1),X26) ) ),
    inference(forward_demodulation,[],[f1802,f181])).

fof(f181,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f180,f166])).

fof(f180,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f107,f179])).

fof(f179,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f167,f44])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f167,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f52,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f103,f50])).

fof(f103,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(resolution,[],[f46,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f53])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1802,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X26) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X26)) ) ),
    inference(resolution,[],[f191,f189])).

fof(f189,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f166,f108])).

fof(f108,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f50,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f191,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f166,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:02:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5822)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5826)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (5820)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (5819)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (5843)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (5834)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (5848)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (5821)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (5836)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (5817)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (5828)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (5824)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (5841)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (5845)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (5832)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (5818)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (5842)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (5831)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (5816)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (5840)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (5844)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (5846)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (5833)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (5839)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (5833)Refutation not found, incomplete strategy% (5833)------------------------------
% 0.21/0.55  % (5833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5833)Memory used [KB]: 10746
% 0.21/0.55  % (5833)Time elapsed: 0.139 s
% 0.21/0.55  % (5833)------------------------------
% 0.21/0.55  % (5833)------------------------------
% 0.21/0.55  % (5835)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (5825)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (5837)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (5830)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (5827)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (5823)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.06/0.64  % (5834)Refutation found. Thanks to Tanya!
% 2.06/0.64  % SZS status Theorem for theBenchmark
% 2.06/0.64  % SZS output start Proof for theBenchmark
% 2.06/0.64  fof(f2321,plain,(
% 2.06/0.64    $false),
% 2.06/0.64    inference(subsumption_resolution,[],[f2320,f49])).
% 2.06/0.64  fof(f49,plain,(
% 2.06/0.64    sK3 != k2_funct_1(sK2)),
% 2.06/0.64    inference(cnf_transformation,[],[f21])).
% 2.06/0.64  fof(f21,plain,(
% 2.06/0.64    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.06/0.64    inference(flattening,[],[f20])).
% 2.06/0.64  fof(f20,plain,(
% 2.06/0.64    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.06/0.64    inference(ennf_transformation,[],[f19])).
% 2.06/0.64  fof(f19,negated_conjecture,(
% 2.06/0.64    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.06/0.64    inference(negated_conjecture,[],[f18])).
% 2.06/0.64  fof(f18,conjecture,(
% 2.06/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.06/0.64  fof(f2320,plain,(
% 2.06/0.64    sK3 = k2_funct_1(sK2)),
% 2.06/0.64    inference(forward_demodulation,[],[f2317,f202])).
% 2.06/0.64  fof(f202,plain,(
% 2.06/0.64    sK2 = k7_relat_1(sK2,sK0)),
% 2.06/0.64    inference(subsumption_resolution,[],[f201,f166])).
% 2.06/0.64  fof(f166,plain,(
% 2.06/0.64    v1_relat_1(sK2)),
% 2.06/0.64    inference(resolution,[],[f52,f68])).
% 2.06/0.64  fof(f68,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f32])).
% 2.06/0.64  fof(f32,plain,(
% 2.06/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.64    inference(ennf_transformation,[],[f10])).
% 2.06/0.64  fof(f10,axiom,(
% 2.06/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.06/0.64  fof(f52,plain,(
% 2.06/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.64    inference(cnf_transformation,[],[f21])).
% 2.06/0.64  fof(f201,plain,(
% 2.06/0.64    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK0)),
% 2.06/0.64    inference(resolution,[],[f168,f67])).
% 2.06/0.64  fof(f67,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 2.06/0.64    inference(cnf_transformation,[],[f31])).
% 2.06/0.64  fof(f31,plain,(
% 2.06/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.06/0.64    inference(flattening,[],[f30])).
% 2.06/0.64  fof(f30,plain,(
% 2.06/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.06/0.64    inference(ennf_transformation,[],[f1])).
% 2.06/0.64  fof(f1,axiom,(
% 2.06/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.06/0.64  fof(f168,plain,(
% 2.06/0.64    v4_relat_1(sK2,sK0)),
% 2.06/0.64    inference(resolution,[],[f52,f70])).
% 2.06/0.64  fof(f70,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f34])).
% 2.06/0.64  fof(f34,plain,(
% 2.06/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.64    inference(ennf_transformation,[],[f11])).
% 2.06/0.64  fof(f11,axiom,(
% 2.06/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.06/0.64  fof(f2317,plain,(
% 2.06/0.64    sK3 = k2_funct_1(k7_relat_1(sK2,sK0))),
% 2.06/0.64    inference(superposition,[],[f2257,f434])).
% 2.06/0.64  fof(f434,plain,(
% 2.06/0.64    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(k7_relat_1(sK2,X0))) )),
% 2.06/0.64    inference(forward_demodulation,[],[f433,f200])).
% 2.06/0.64  fof(f200,plain,(
% 2.06/0.64    ( ! [X8] : (k7_relat_1(sK2,X8) = k5_relat_1(k6_partfun1(X8),sK2)) )),
% 2.06/0.64    inference(resolution,[],[f166,f85])).
% 2.06/0.64  fof(f85,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 2.06/0.64    inference(definition_unfolding,[],[f66,f53])).
% 2.06/0.64  fof(f53,plain,(
% 2.06/0.64    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f17])).
% 2.06/0.64  fof(f17,axiom,(
% 2.06/0.64    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.06/0.64  fof(f66,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f29])).
% 2.06/0.64  fof(f29,plain,(
% 2.06/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.06/0.64    inference(ennf_transformation,[],[f3])).
% 2.06/0.64  fof(f3,axiom,(
% 2.06/0.64    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.06/0.64  fof(f433,plain,(
% 2.06/0.64    ( ! [X0] : (k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0))) )),
% 2.06/0.64    inference(forward_demodulation,[],[f432,f77])).
% 2.06/0.64  fof(f77,plain,(
% 2.06/0.64    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 2.06/0.64    inference(definition_unfolding,[],[f54,f53,f53])).
% 2.06/0.64  fof(f54,plain,(
% 2.06/0.64    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f9])).
% 2.06/0.64  fof(f9,axiom,(
% 2.06/0.64    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 2.06/0.64  fof(f432,plain,(
% 2.06/0.64    ( ! [X0] : (k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0)))) )),
% 2.06/0.64    inference(subsumption_resolution,[],[f431,f82])).
% 2.06/0.64  fof(f82,plain,(
% 2.06/0.64    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.06/0.64    inference(definition_unfolding,[],[f58,f53])).
% 2.06/0.64  fof(f58,plain,(
% 2.06/0.64    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f5])).
% 2.06/0.64  fof(f5,axiom,(
% 2.06/0.64    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.06/0.64  fof(f431,plain,(
% 2.06/0.64    ( ! [X0] : (~v1_relat_1(k6_partfun1(X0)) | k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0)))) )),
% 2.06/0.64    inference(subsumption_resolution,[],[f430,f166])).
% 2.06/0.64  fof(f430,plain,(
% 2.06/0.64    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(k6_partfun1(X0)) | k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0)))) )),
% 2.06/0.64    inference(subsumption_resolution,[],[f427,f81])).
% 2.06/0.64  fof(f81,plain,(
% 2.06/0.64    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.06/0.64    inference(definition_unfolding,[],[f59,f53])).
% 2.06/0.64  fof(f59,plain,(
% 2.06/0.64    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f5])).
% 2.06/0.64  fof(f427,plain,(
% 2.06/0.64    ( ! [X0] : (~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(k6_partfun1(X0)) | k2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(k6_partfun1(X0)))) )),
% 2.06/0.64    inference(resolution,[],[f104,f79])).
% 2.06/0.64  fof(f79,plain,(
% 2.06/0.64    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.06/0.64    inference(definition_unfolding,[],[f57,f53])).
% 2.06/0.64  fof(f57,plain,(
% 2.06/0.64    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f6])).
% 2.06/0.64  fof(f6,axiom,(
% 2.06/0.64    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.06/0.64  fof(f104,plain,(
% 2.06/0.64    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | k2_funct_1(k5_relat_1(X0,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X0))) )),
% 2.06/0.64    inference(subsumption_resolution,[],[f100,f50])).
% 2.06/0.64  fof(f50,plain,(
% 2.06/0.64    v1_funct_1(sK2)),
% 2.06/0.64    inference(cnf_transformation,[],[f21])).
% 2.06/0.64  fof(f100,plain,(
% 2.06/0.64    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(X0) | k2_funct_1(k5_relat_1(X0,sK2)) = k5_relat_1(k2_funct_1(sK2),k2_funct_1(X0))) )),
% 2.06/0.64    inference(resolution,[],[f46,f65])).
% 2.06/0.64  fof(f65,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f28])).
% 2.06/0.64  fof(f28,plain,(
% 2.06/0.64    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.64    inference(flattening,[],[f27])).
% 2.06/0.64  fof(f27,plain,(
% 2.06/0.64    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/0.64    inference(ennf_transformation,[],[f8])).
% 2.06/0.64  fof(f8,axiom,(
% 2.06/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).
% 2.06/0.64  fof(f46,plain,(
% 2.06/0.64    v2_funct_1(sK2)),
% 2.06/0.64    inference(cnf_transformation,[],[f21])).
% 2.06/0.65  fof(f2257,plain,(
% 2.06/0.65    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 2.06/0.65    inference(forward_demodulation,[],[f2256,f151])).
% 2.06/0.65  fof(f151,plain,(
% 2.06/0.65    sK3 = k7_relat_1(sK3,sK1)),
% 2.06/0.65    inference(subsumption_resolution,[],[f150,f121])).
% 2.06/0.65  fof(f121,plain,(
% 2.06/0.65    v1_relat_1(sK3)),
% 2.06/0.65    inference(resolution,[],[f43,f68])).
% 2.06/0.65  fof(f43,plain,(
% 2.06/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.06/0.65    inference(cnf_transformation,[],[f21])).
% 2.06/0.65  fof(f150,plain,(
% 2.06/0.65    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK1)),
% 2.06/0.65    inference(resolution,[],[f123,f67])).
% 2.06/0.65  fof(f123,plain,(
% 2.06/0.65    v4_relat_1(sK3,sK1)),
% 2.06/0.65    inference(resolution,[],[f43,f70])).
% 2.06/0.65  fof(f2256,plain,(
% 2.06/0.65    k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 2.06/0.65    inference(forward_demodulation,[],[f2255,f965])).
% 2.06/0.65  fof(f965,plain,(
% 2.06/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.06/0.65    inference(resolution,[],[f964,f612])).
% 2.06/0.65  fof(f612,plain,(
% 2.06/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.06/0.65    inference(forward_demodulation,[],[f609,f606])).
% 2.06/0.65  fof(f606,plain,(
% 2.06/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.06/0.65    inference(subsumption_resolution,[],[f596,f50])).
% 2.06/0.65  fof(f596,plain,(
% 2.06/0.65    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.06/0.65    inference(resolution,[],[f135,f52])).
% 2.06/0.65  fof(f135,plain,(
% 2.06/0.65    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(X5) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 2.06/0.65    inference(subsumption_resolution,[],[f128,f41])).
% 2.06/0.65  fof(f41,plain,(
% 2.06/0.65    v1_funct_1(sK3)),
% 2.06/0.65    inference(cnf_transformation,[],[f21])).
% 2.06/0.65  fof(f128,plain,(
% 2.06/0.65    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK3) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 2.06/0.65    inference(resolution,[],[f43,f74])).
% 2.06/0.65  fof(f74,plain,(
% 2.06/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 2.06/0.65    inference(cnf_transformation,[],[f38])).
% 2.06/0.65  fof(f38,plain,(
% 2.06/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.06/0.65    inference(flattening,[],[f37])).
% 2.06/0.65  fof(f37,plain,(
% 2.06/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.06/0.65    inference(ennf_transformation,[],[f16])).
% 2.06/0.65  fof(f16,axiom,(
% 2.06/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.06/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.06/0.65  fof(f609,plain,(
% 2.06/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.06/0.65    inference(backward_demodulation,[],[f188,f606])).
% 2.06/0.65  fof(f188,plain,(
% 2.06/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.06/0.65    inference(subsumption_resolution,[],[f186,f78])).
% 2.06/0.65  fof(f78,plain,(
% 2.06/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.06/0.65    inference(definition_unfolding,[],[f55,f53])).
% 2.06/0.65  fof(f55,plain,(
% 2.06/0.65    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.06/0.65    inference(cnf_transformation,[],[f14])).
% 2.06/0.65  fof(f14,axiom,(
% 2.06/0.65    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.06/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.06/0.65  fof(f186,plain,(
% 2.06/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.06/0.65    inference(resolution,[],[f45,f73])).
% 2.06/0.65  fof(f73,plain,(
% 2.06/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.06/0.65    inference(cnf_transformation,[],[f36])).
% 2.06/0.65  fof(f36,plain,(
% 2.06/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.65    inference(flattening,[],[f35])).
% 2.06/0.66  fof(f35,plain,(
% 2.06/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.06/0.66    inference(ennf_transformation,[],[f13])).
% 2.06/0.66  fof(f13,axiom,(
% 2.06/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.06/0.66  fof(f45,plain,(
% 2.06/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.06/0.66    inference(cnf_transformation,[],[f21])).
% 2.06/0.66  fof(f964,plain,(
% 2.06/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.06/0.66    inference(subsumption_resolution,[],[f963,f43])).
% 2.06/0.66  fof(f963,plain,(
% 2.06/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.06/0.66    inference(subsumption_resolution,[],[f962,f41])).
% 2.06/0.66  fof(f962,plain,(
% 2.06/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.06/0.66    inference(subsumption_resolution,[],[f961,f52])).
% 2.06/0.66  fof(f961,plain,(
% 2.06/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.06/0.66    inference(subsumption_resolution,[],[f960,f50])).
% 2.06/0.66  fof(f960,plain,(
% 2.06/0.66    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.06/0.66    inference(superposition,[],[f76,f606])).
% 2.06/0.66  fof(f76,plain,(
% 2.06/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 2.06/0.66    inference(cnf_transformation,[],[f40])).
% 2.06/0.66  fof(f40,plain,(
% 2.06/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.06/0.66    inference(flattening,[],[f39])).
% 2.06/0.66  fof(f39,plain,(
% 2.06/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.06/0.66    inference(ennf_transformation,[],[f15])).
% 2.06/0.66  fof(f15,axiom,(
% 2.06/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.06/0.66  fof(f2255,plain,(
% 2.06/0.66    k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))),
% 2.06/0.66    inference(forward_demodulation,[],[f2065,f149])).
% 2.06/0.66  fof(f149,plain,(
% 2.06/0.66    ( ! [X8] : (k7_relat_1(sK3,X8) = k5_relat_1(k6_partfun1(X8),sK3)) )),
% 2.06/0.66    inference(resolution,[],[f121,f85])).
% 2.06/0.66  fof(f2065,plain,(
% 2.06/0.66    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.06/0.66    inference(resolution,[],[f1811,f121])).
% 2.06/0.66  fof(f1811,plain,(
% 2.06/0.66    ( ! [X26] : (~v1_relat_1(X26) | k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X26)) = k5_relat_1(k6_partfun1(sK1),X26)) )),
% 2.06/0.66    inference(forward_demodulation,[],[f1802,f181])).
% 2.06/0.66  fof(f181,plain,(
% 2.06/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.06/0.66    inference(subsumption_resolution,[],[f180,f166])).
% 2.06/0.66  fof(f180,plain,(
% 2.06/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~v1_relat_1(sK2)),
% 2.06/0.66    inference(backward_demodulation,[],[f107,f179])).
% 2.06/0.66  fof(f179,plain,(
% 2.06/0.66    sK1 = k2_relat_1(sK2)),
% 2.06/0.66    inference(forward_demodulation,[],[f167,f44])).
% 2.06/0.66  fof(f44,plain,(
% 2.06/0.66    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.06/0.66    inference(cnf_transformation,[],[f21])).
% 2.06/0.66  fof(f167,plain,(
% 2.06/0.66    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.06/0.66    inference(resolution,[],[f52,f69])).
% 2.06/0.66  fof(f69,plain,(
% 2.06/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f33])).
% 2.06/0.66  fof(f33,plain,(
% 2.06/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.66    inference(ennf_transformation,[],[f12])).
% 2.06/0.66  fof(f12,axiom,(
% 2.06/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.06/0.66  fof(f107,plain,(
% 2.06/0.66    ~v1_relat_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))),
% 2.06/0.66    inference(subsumption_resolution,[],[f103,f50])).
% 2.06/0.66  fof(f103,plain,(
% 2.06/0.66    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))),
% 2.06/0.66    inference(resolution,[],[f46,f83])).
% 2.06/0.66  fof(f83,plain,(
% 2.06/0.66    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))) )),
% 2.06/0.66    inference(definition_unfolding,[],[f64,f53])).
% 2.06/0.66  fof(f64,plain,(
% 2.06/0.66    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 2.06/0.66    inference(cnf_transformation,[],[f26])).
% 2.06/0.66  fof(f26,plain,(
% 2.06/0.66    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.66    inference(flattening,[],[f25])).
% 2.06/0.66  fof(f25,plain,(
% 2.06/0.66    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/0.66    inference(ennf_transformation,[],[f7])).
% 2.06/0.66  fof(f7,axiom,(
% 2.06/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.06/0.66  fof(f1802,plain,(
% 2.06/0.66    ( ! [X26] : (~v1_relat_1(X26) | k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X26) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X26))) )),
% 2.06/0.66    inference(resolution,[],[f191,f189])).
% 2.06/0.66  fof(f189,plain,(
% 2.06/0.66    v1_relat_1(k2_funct_1(sK2))),
% 2.06/0.66    inference(resolution,[],[f166,f108])).
% 2.06/0.66  fof(f108,plain,(
% 2.06/0.66    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 2.06/0.66    inference(resolution,[],[f50,f61])).
% 2.06/0.66  fof(f61,plain,(
% 2.06/0.66    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 2.06/0.66    inference(cnf_transformation,[],[f24])).
% 2.06/0.66  fof(f24,plain,(
% 2.06/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.66    inference(flattening,[],[f23])).
% 2.06/0.66  fof(f23,plain,(
% 2.06/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/0.66    inference(ennf_transformation,[],[f4])).
% 2.06/0.66  fof(f4,axiom,(
% 2.06/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.06/0.66  fof(f191,plain,(
% 2.06/0.66    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3))) )),
% 2.06/0.66    inference(resolution,[],[f166,f60])).
% 2.06/0.66  fof(f60,plain,(
% 2.06/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.06/0.66    inference(cnf_transformation,[],[f22])).
% 2.06/0.66  fof(f22,plain,(
% 2.06/0.66    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.06/0.66    inference(ennf_transformation,[],[f2])).
% 2.06/0.66  fof(f2,axiom,(
% 2.06/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.06/0.66  % SZS output end Proof for theBenchmark
% 2.06/0.66  % (5834)------------------------------
% 2.06/0.66  % (5834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.66  % (5834)Termination reason: Refutation
% 2.06/0.66  
% 2.06/0.66  % (5834)Memory used [KB]: 3198
% 2.06/0.66  % (5834)Time elapsed: 0.233 s
% 2.06/0.66  % (5834)------------------------------
% 2.06/0.66  % (5834)------------------------------
% 2.06/0.66  % (5813)Success in time 0.296 s
%------------------------------------------------------------------------------
