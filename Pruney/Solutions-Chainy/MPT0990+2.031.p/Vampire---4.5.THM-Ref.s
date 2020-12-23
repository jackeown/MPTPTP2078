%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:33 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 359 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  361 (2510 expanded)
%              Number of equality atoms :  138 ( 836 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1530,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1529,f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1529,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f1528,f214])).

fof(f214,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(forward_demodulation,[],[f213,f195])).

fof(f195,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f181,f155])).

fof(f155,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f154,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f154,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f147,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f147,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f46,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f46,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f181,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f47,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f213,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f180,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f180,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f47,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1528,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(forward_demodulation,[],[f1527,f285])).

fof(f285,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f283,f249])).

fof(f249,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f248,f232])).

fof(f232,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f56,f73])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f248,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f124,f247])).

fof(f247,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f233,f178])).

fof(f178,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f177,f52])).

fof(f52,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f158,f56])).

fof(f158,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f55,f80])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f233,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f56,f74])).

fof(f124,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f116,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f116,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f50,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f283,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) ),
    inference(resolution,[],[f254,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f62,f57])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f254,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f232,f129])).

fof(f129,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f54,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1527,plain,(
    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f1520,f935])).

fof(f935,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f934,f619])).

fof(f619,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f616,f613])).

fof(f613,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f608,f54])).

fof(f608,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f197,f56])).

fof(f197,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f189,f45])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f189,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(resolution,[],[f47,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f616,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f271,f613])).

fof(f271,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f269,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f269,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f49,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f49,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f934,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f933,f47])).

fof(f933,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f932,f45])).

fof(f932,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f931,f56])).

fof(f931,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f930,f54])).

fof(f930,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f87,f613])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1520,plain,(
    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f1392,f180])).

fof(f1392,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X13)) = k5_relat_1(k6_partfun1(sK1),X13) ) ),
    inference(forward_demodulation,[],[f1385,f172])).

fof(f172,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f171,f52])).

fof(f171,plain,
    ( k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f170,f50])).

fof(f170,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f169,f48])).

fof(f48,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f169,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f168,f56])).

fof(f168,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f157,f54])).

fof(f157,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(resolution,[],[f55,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f1385,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X13) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X13)) ) ),
    inference(resolution,[],[f256,f254])).

fof(f256,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f232,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (1220050944)
% 0.21/0.37  ipcrm: permission denied for id (1222180866)
% 0.21/0.38  ipcrm: permission denied for id (1222213635)
% 0.21/0.38  ipcrm: permission denied for id (1222246404)
% 0.21/0.38  ipcrm: permission denied for id (1222279173)
% 0.21/0.38  ipcrm: permission denied for id (1227456519)
% 0.21/0.38  ipcrm: permission denied for id (1225588744)
% 0.21/0.38  ipcrm: permission denied for id (1225621513)
% 0.21/0.38  ipcrm: permission denied for id (1222443018)
% 0.21/0.39  ipcrm: permission denied for id (1222475787)
% 0.21/0.39  ipcrm: permission denied for id (1222508556)
% 0.21/0.39  ipcrm: permission denied for id (1222541325)
% 0.21/0.39  ipcrm: permission denied for id (1225654286)
% 0.21/0.39  ipcrm: permission denied for id (1225687055)
% 0.21/0.39  ipcrm: permission denied for id (1225752593)
% 0.21/0.39  ipcrm: permission denied for id (1225785362)
% 0.21/0.40  ipcrm: permission denied for id (1222737939)
% 0.21/0.40  ipcrm: permission denied for id (1227522068)
% 0.21/0.40  ipcrm: permission denied for id (1225850901)
% 0.21/0.40  ipcrm: permission denied for id (1222869014)
% 0.21/0.40  ipcrm: permission denied for id (1222901783)
% 0.21/0.40  ipcrm: permission denied for id (1222934552)
% 0.21/0.40  ipcrm: permission denied for id (1222967321)
% 0.21/0.40  ipcrm: permission denied for id (1223000090)
% 0.21/0.41  ipcrm: permission denied for id (1223032859)
% 0.21/0.41  ipcrm: permission denied for id (1225883676)
% 0.21/0.41  ipcrm: permission denied for id (1225916445)
% 0.21/0.41  ipcrm: permission denied for id (1223131166)
% 0.21/0.41  ipcrm: permission denied for id (1225949215)
% 0.21/0.41  ipcrm: permission denied for id (1225981984)
% 0.21/0.41  ipcrm: permission denied for id (1223229473)
% 0.21/0.41  ipcrm: permission denied for id (1223262242)
% 0.21/0.42  ipcrm: permission denied for id (1223360549)
% 0.21/0.42  ipcrm: permission denied for id (1227653159)
% 0.21/0.42  ipcrm: permission denied for id (1223491625)
% 0.21/0.42  ipcrm: permission denied for id (1227718698)
% 0.21/0.43  ipcrm: permission denied for id (1220706347)
% 0.21/0.43  ipcrm: permission denied for id (1223557164)
% 0.21/0.43  ipcrm: permission denied for id (1223589933)
% 0.21/0.43  ipcrm: permission denied for id (1223622702)
% 0.21/0.43  ipcrm: permission denied for id (1220771887)
% 0.21/0.43  ipcrm: permission denied for id (1223655472)
% 0.21/0.43  ipcrm: permission denied for id (1220804657)
% 0.21/0.43  ipcrm: permission denied for id (1226211378)
% 0.21/0.44  ipcrm: permission denied for id (1220837427)
% 0.21/0.44  ipcrm: permission denied for id (1227751476)
% 0.21/0.44  ipcrm: permission denied for id (1220870197)
% 0.21/0.44  ipcrm: permission denied for id (1227784246)
% 0.21/0.44  ipcrm: permission denied for id (1226309687)
% 0.21/0.44  ipcrm: permission denied for id (1223819320)
% 0.21/0.44  ipcrm: permission denied for id (1220935737)
% 0.21/0.44  ipcrm: permission denied for id (1220968506)
% 0.21/0.45  ipcrm: permission denied for id (1223852091)
% 0.21/0.45  ipcrm: permission denied for id (1221001276)
% 0.21/0.45  ipcrm: permission denied for id (1221034045)
% 0.21/0.45  ipcrm: permission denied for id (1227849791)
% 0.21/0.45  ipcrm: permission denied for id (1221066816)
% 0.21/0.45  ipcrm: permission denied for id (1221099586)
% 0.21/0.45  ipcrm: permission denied for id (1223983171)
% 0.21/0.46  ipcrm: permission denied for id (1221132356)
% 0.21/0.46  ipcrm: permission denied for id (1224015941)
% 0.21/0.46  ipcrm: permission denied for id (1226440774)
% 0.21/0.46  ipcrm: permission denied for id (1224081479)
% 0.21/0.46  ipcrm: permission denied for id (1221165129)
% 0.21/0.46  ipcrm: permission denied for id (1224147018)
% 0.21/0.47  ipcrm: permission denied for id (1227948107)
% 0.21/0.47  ipcrm: permission denied for id (1221197900)
% 0.21/0.47  ipcrm: permission denied for id (1224212557)
% 0.21/0.47  ipcrm: permission denied for id (1221230670)
% 0.21/0.47  ipcrm: permission denied for id (1221263439)
% 0.21/0.47  ipcrm: permission denied for id (1227980880)
% 0.21/0.47  ipcrm: permission denied for id (1224278097)
% 0.21/0.47  ipcrm: permission denied for id (1226571858)
% 0.21/0.48  ipcrm: permission denied for id (1224343635)
% 0.21/0.48  ipcrm: permission denied for id (1226637396)
% 0.21/0.48  ipcrm: permission denied for id (1226702934)
% 0.21/0.48  ipcrm: permission denied for id (1221394519)
% 0.21/0.48  ipcrm: permission denied for id (1224474712)
% 0.21/0.48  ipcrm: permission denied for id (1228046425)
% 0.21/0.49  ipcrm: permission denied for id (1224540250)
% 0.21/0.49  ipcrm: permission denied for id (1228079195)
% 0.21/0.49  ipcrm: permission denied for id (1228111964)
% 0.21/0.49  ipcrm: permission denied for id (1221525598)
% 0.21/0.50  ipcrm: permission denied for id (1221558368)
% 0.21/0.50  ipcrm: permission denied for id (1226899553)
% 0.21/0.50  ipcrm: permission denied for id (1228210274)
% 0.21/0.50  ipcrm: permission denied for id (1221591140)
% 0.21/0.50  ipcrm: permission denied for id (1224802405)
% 0.21/0.50  ipcrm: permission denied for id (1221623910)
% 0.21/0.51  ipcrm: permission denied for id (1224835175)
% 0.21/0.51  ipcrm: permission denied for id (1224867944)
% 0.21/0.51  ipcrm: permission denied for id (1226997865)
% 0.21/0.51  ipcrm: permission denied for id (1221689450)
% 0.21/0.51  ipcrm: permission denied for id (1221722219)
% 0.21/0.51  ipcrm: permission denied for id (1228275820)
% 0.21/0.52  ipcrm: permission denied for id (1221754989)
% 0.21/0.52  ipcrm: permission denied for id (1221787759)
% 0.21/0.52  ipcrm: permission denied for id (1228341360)
% 0.21/0.52  ipcrm: permission denied for id (1227128945)
% 0.21/0.52  ipcrm: permission denied for id (1227161714)
% 0.21/0.52  ipcrm: permission denied for id (1225130099)
% 0.21/0.53  ipcrm: permission denied for id (1227194484)
% 0.21/0.53  ipcrm: permission denied for id (1227260022)
% 0.21/0.53  ipcrm: permission denied for id (1225261175)
% 0.21/0.53  ipcrm: permission denied for id (1225293944)
% 0.21/0.53  ipcrm: permission denied for id (1227292793)
% 0.21/0.54  ipcrm: permission denied for id (1227325562)
% 0.21/0.54  ipcrm: permission denied for id (1225392251)
% 0.21/0.54  ipcrm: permission denied for id (1222082685)
% 0.21/0.54  ipcrm: permission denied for id (1225457790)
% 0.21/0.54  ipcrm: permission denied for id (1222115455)
% 0.40/0.69  % (6089)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.40/0.69  % (6097)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.40/0.75  % (6100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.40/0.76  % (6092)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.40/0.76  % (6083)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.40/0.79  % (6077)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.40/0.79  % (6079)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.40/0.79  % (6076)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.40/0.79  % (6078)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.40/0.79  % (6084)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.40/0.80  % (6081)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.40/0.80  % (6085)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.40/0.80  % (6086)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.40/0.80  % (6091)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.40/0.81  % (6093)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.40/0.81  % (6099)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.40/0.81  % (6098)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.40/0.81  % (6102)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.40/0.81  % (6094)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.40/0.82  % (6104)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.40/0.82  % (6082)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.40/0.82  % (6095)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.40/0.82  % (6075)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.40/0.82  % (6080)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.40/0.82  % (6101)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.40/0.82  % (6091)Refutation not found, incomplete strategy% (6091)------------------------------
% 0.40/0.82  % (6091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.82  % (6091)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.82  
% 0.40/0.82  % (6091)Memory used [KB]: 10746
% 0.40/0.82  % (6091)Time elapsed: 0.183 s
% 0.40/0.82  % (6091)------------------------------
% 0.40/0.82  % (6091)------------------------------
% 0.40/0.82  % (6103)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.40/0.83  % (6090)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.40/0.83  % (6088)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.47/0.83  % (6096)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.47/0.83  % (6087)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.47/0.84  % (6092)Refutation found. Thanks to Tanya!
% 0.47/0.84  % SZS status Theorem for theBenchmark
% 0.47/0.86  % SZS output start Proof for theBenchmark
% 0.47/0.86  fof(f1530,plain,(
% 0.47/0.86    $false),
% 0.47/0.86    inference(subsumption_resolution,[],[f1529,f53])).
% 0.47/0.86  fof(f53,plain,(
% 0.47/0.86    sK3 != k2_funct_1(sK2)),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f21,plain,(
% 0.47/0.86    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.47/0.86    inference(flattening,[],[f20])).
% 0.47/0.86  fof(f20,plain,(
% 0.47/0.86    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.47/0.86    inference(ennf_transformation,[],[f19])).
% 0.47/0.86  fof(f19,negated_conjecture,(
% 0.47/0.86    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.47/0.86    inference(negated_conjecture,[],[f18])).
% 0.47/0.86  fof(f18,conjecture,(
% 0.47/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.47/0.86  fof(f1529,plain,(
% 0.47/0.86    sK3 = k2_funct_1(sK2)),
% 0.47/0.86    inference(forward_demodulation,[],[f1528,f214])).
% 0.47/0.86  fof(f214,plain,(
% 0.47/0.86    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 0.47/0.86    inference(forward_demodulation,[],[f213,f195])).
% 0.47/0.86  fof(f195,plain,(
% 0.47/0.86    sK1 = k1_relat_1(sK3)),
% 0.47/0.86    inference(forward_demodulation,[],[f181,f155])).
% 0.47/0.86  fof(f155,plain,(
% 0.47/0.86    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.47/0.86    inference(subsumption_resolution,[],[f154,f51])).
% 0.47/0.86  fof(f51,plain,(
% 0.47/0.86    k1_xboole_0 != sK0),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f154,plain,(
% 0.47/0.86    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.47/0.86    inference(subsumption_resolution,[],[f147,f47])).
% 0.47/0.86  fof(f47,plain,(
% 0.47/0.86    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f147,plain,(
% 0.47/0.86    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.47/0.86    inference(resolution,[],[f46,f80])).
% 0.47/0.86  fof(f80,plain,(
% 0.47/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.47/0.86    inference(cnf_transformation,[],[f36])).
% 0.47/0.86  fof(f36,plain,(
% 0.47/0.86    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.47/0.86    inference(flattening,[],[f35])).
% 0.47/0.86  fof(f35,plain,(
% 0.47/0.86    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.47/0.86    inference(ennf_transformation,[],[f12])).
% 0.47/0.86  fof(f12,axiom,(
% 0.47/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.47/0.86  fof(f46,plain,(
% 0.47/0.86    v1_funct_2(sK3,sK1,sK0)),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f181,plain,(
% 0.47/0.86    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 0.47/0.86    inference(resolution,[],[f47,f74])).
% 0.47/0.86  fof(f74,plain,(
% 0.47/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.47/0.86    inference(cnf_transformation,[],[f34])).
% 0.47/0.86  fof(f34,plain,(
% 0.47/0.86    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.47/0.86    inference(ennf_transformation,[],[f10])).
% 0.47/0.86  fof(f10,axiom,(
% 0.47/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.47/0.86  fof(f213,plain,(
% 0.47/0.86    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 0.47/0.86    inference(resolution,[],[f180,f91])).
% 0.47/0.86  fof(f91,plain,(
% 0.47/0.86    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 0.47/0.86    inference(definition_unfolding,[],[f63,f57])).
% 0.47/0.86  fof(f57,plain,(
% 0.47/0.86    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.47/0.86    inference(cnf_transformation,[],[f16])).
% 0.47/0.86  fof(f16,axiom,(
% 0.47/0.86    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.47/0.86  fof(f63,plain,(
% 0.47/0.86    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.47/0.86    inference(cnf_transformation,[],[f23])).
% 0.47/0.86  fof(f23,plain,(
% 0.47/0.86    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.47/0.86    inference(ennf_transformation,[],[f3])).
% 0.47/0.86  fof(f3,axiom,(
% 0.47/0.86    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.47/0.86  fof(f180,plain,(
% 0.47/0.86    v1_relat_1(sK3)),
% 0.47/0.86    inference(resolution,[],[f47,f73])).
% 0.47/0.86  fof(f73,plain,(
% 0.47/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.47/0.86    inference(cnf_transformation,[],[f33])).
% 0.47/0.86  fof(f33,plain,(
% 0.47/0.86    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.47/0.86    inference(ennf_transformation,[],[f9])).
% 0.47/0.86  fof(f9,axiom,(
% 0.47/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.47/0.86  fof(f1528,plain,(
% 0.47/0.86    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 0.47/0.86    inference(forward_demodulation,[],[f1527,f285])).
% 0.47/0.86  fof(f285,plain,(
% 0.47/0.86    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 0.47/0.86    inference(forward_demodulation,[],[f283,f249])).
% 0.47/0.86  fof(f249,plain,(
% 0.47/0.86    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.47/0.86    inference(subsumption_resolution,[],[f248,f232])).
% 0.47/0.86  fof(f232,plain,(
% 0.47/0.86    v1_relat_1(sK2)),
% 0.47/0.86    inference(resolution,[],[f56,f73])).
% 0.47/0.86  fof(f56,plain,(
% 0.47/0.86    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f248,plain,(
% 0.47/0.86    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.47/0.86    inference(backward_demodulation,[],[f124,f247])).
% 0.47/0.86  fof(f247,plain,(
% 0.47/0.86    sK0 = k1_relat_1(sK2)),
% 0.47/0.86    inference(forward_demodulation,[],[f233,f178])).
% 0.47/0.86  fof(f178,plain,(
% 0.47/0.86    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.47/0.86    inference(subsumption_resolution,[],[f177,f52])).
% 0.47/0.86  fof(f52,plain,(
% 0.47/0.86    k1_xboole_0 != sK1),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f177,plain,(
% 0.47/0.86    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.47/0.86    inference(subsumption_resolution,[],[f158,f56])).
% 0.47/0.86  fof(f158,plain,(
% 0.47/0.86    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.47/0.86    inference(resolution,[],[f55,f80])).
% 0.47/0.86  fof(f55,plain,(
% 0.47/0.86    v1_funct_2(sK2,sK0,sK1)),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f233,plain,(
% 0.47/0.86    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.47/0.86    inference(resolution,[],[f56,f74])).
% 0.47/0.86  fof(f124,plain,(
% 0.47/0.86    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.47/0.86    inference(subsumption_resolution,[],[f116,f54])).
% 0.47/0.86  fof(f54,plain,(
% 0.47/0.86    v1_funct_1(sK2)),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f116,plain,(
% 0.47/0.86    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.47/0.86    inference(resolution,[],[f50,f68])).
% 0.47/0.86  fof(f68,plain,(
% 0.47/0.86    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.47/0.86    inference(cnf_transformation,[],[f28])).
% 0.47/0.86  fof(f28,plain,(
% 0.47/0.86    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.47/0.86    inference(flattening,[],[f27])).
% 0.47/0.86  fof(f27,plain,(
% 0.47/0.86    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.47/0.86    inference(ennf_transformation,[],[f6])).
% 0.47/0.86  fof(f6,axiom,(
% 0.47/0.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.47/0.86  fof(f50,plain,(
% 0.47/0.86    v2_funct_1(sK2)),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f283,plain,(
% 0.47/0.86    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))),
% 0.47/0.86    inference(resolution,[],[f254,f90])).
% 0.47/0.86  fof(f90,plain,(
% 0.47/0.86    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 0.47/0.86    inference(definition_unfolding,[],[f62,f57])).
% 0.47/0.86  fof(f62,plain,(
% 0.47/0.86    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.47/0.86    inference(cnf_transformation,[],[f22])).
% 0.47/0.86  fof(f22,plain,(
% 0.47/0.86    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.47/0.86    inference(ennf_transformation,[],[f4])).
% 0.47/0.86  fof(f4,axiom,(
% 0.47/0.86    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.47/0.86  fof(f254,plain,(
% 0.47/0.86    v1_relat_1(k2_funct_1(sK2))),
% 0.47/0.86    inference(resolution,[],[f232,f129])).
% 0.47/0.86  fof(f129,plain,(
% 0.47/0.86    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.47/0.86    inference(resolution,[],[f54,f65])).
% 0.47/0.86  fof(f65,plain,(
% 0.47/0.86    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.47/0.86    inference(cnf_transformation,[],[f26])).
% 0.47/0.86  fof(f26,plain,(
% 0.47/0.86    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.47/0.86    inference(flattening,[],[f25])).
% 0.47/0.86  fof(f25,plain,(
% 0.47/0.86    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.47/0.86    inference(ennf_transformation,[],[f5])).
% 0.47/0.86  fof(f5,axiom,(
% 0.47/0.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.47/0.86  fof(f1527,plain,(
% 0.47/0.86    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 0.47/0.86    inference(forward_demodulation,[],[f1520,f935])).
% 0.47/0.86  fof(f935,plain,(
% 0.47/0.86    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.47/0.86    inference(resolution,[],[f934,f619])).
% 0.47/0.86  fof(f619,plain,(
% 0.47/0.86    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.47/0.86    inference(forward_demodulation,[],[f616,f613])).
% 0.47/0.86  fof(f613,plain,(
% 0.47/0.86    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.47/0.86    inference(subsumption_resolution,[],[f608,f54])).
% 0.47/0.86  fof(f608,plain,(
% 0.47/0.86    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.47/0.86    inference(resolution,[],[f197,f56])).
% 0.47/0.86  fof(f197,plain,(
% 0.47/0.86    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(X5) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 0.47/0.86    inference(subsumption_resolution,[],[f189,f45])).
% 0.47/0.86  fof(f45,plain,(
% 0.47/0.86    v1_funct_1(sK3)),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f189,plain,(
% 0.47/0.86    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK3) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 0.47/0.86    inference(resolution,[],[f47,f85])).
% 0.47/0.86  fof(f85,plain,(
% 0.47/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.47/0.86    inference(cnf_transformation,[],[f42])).
% 0.47/0.86  fof(f42,plain,(
% 0.47/0.86    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.47/0.86    inference(flattening,[],[f41])).
% 0.47/0.86  fof(f41,plain,(
% 0.47/0.86    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.47/0.86    inference(ennf_transformation,[],[f15])).
% 0.47/0.86  fof(f15,axiom,(
% 0.47/0.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.47/0.86  fof(f616,plain,(
% 0.47/0.86    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.47/0.86    inference(backward_demodulation,[],[f271,f613])).
% 0.47/0.86  fof(f271,plain,(
% 0.47/0.86    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.47/0.86    inference(subsumption_resolution,[],[f269,f59])).
% 0.47/0.86  fof(f59,plain,(
% 0.47/0.86    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.47/0.86    inference(cnf_transformation,[],[f14])).
% 0.47/0.86  fof(f14,axiom,(
% 0.47/0.86    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.47/0.86  fof(f269,plain,(
% 0.47/0.86    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.47/0.86    inference(resolution,[],[f49,f84])).
% 0.47/0.86  fof(f84,plain,(
% 0.47/0.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.47/0.86    inference(cnf_transformation,[],[f40])).
% 0.47/0.86  fof(f40,plain,(
% 0.47/0.86    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.47/0.86    inference(flattening,[],[f39])).
% 0.47/0.86  fof(f39,plain,(
% 0.47/0.86    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.47/0.86    inference(ennf_transformation,[],[f11])).
% 0.47/0.86  fof(f11,axiom,(
% 0.47/0.86    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.47/0.86  fof(f49,plain,(
% 0.47/0.86    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f934,plain,(
% 0.47/0.86    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.47/0.86    inference(subsumption_resolution,[],[f933,f47])).
% 0.47/0.86  fof(f933,plain,(
% 0.47/0.86    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.47/0.86    inference(subsumption_resolution,[],[f932,f45])).
% 0.47/0.86  fof(f932,plain,(
% 0.47/0.86    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.47/0.86    inference(subsumption_resolution,[],[f931,f56])).
% 0.47/0.86  fof(f931,plain,(
% 0.47/0.86    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.47/0.86    inference(subsumption_resolution,[],[f930,f54])).
% 0.47/0.86  fof(f930,plain,(
% 0.47/0.86    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.47/0.86    inference(superposition,[],[f87,f613])).
% 0.47/0.86  fof(f87,plain,(
% 0.47/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 0.47/0.86    inference(cnf_transformation,[],[f44])).
% 0.47/0.86  fof(f44,plain,(
% 0.47/0.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.47/0.86    inference(flattening,[],[f43])).
% 0.47/0.86  fof(f43,plain,(
% 0.47/0.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.47/0.86    inference(ennf_transformation,[],[f13])).
% 0.47/0.86  fof(f13,axiom,(
% 0.47/0.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.47/0.86  fof(f1520,plain,(
% 0.47/0.86    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))),
% 0.47/0.86    inference(resolution,[],[f1392,f180])).
% 0.47/0.86  fof(f1392,plain,(
% 0.47/0.86    ( ! [X13] : (~v1_relat_1(X13) | k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X13)) = k5_relat_1(k6_partfun1(sK1),X13)) )),
% 0.47/0.86    inference(forward_demodulation,[],[f1385,f172])).
% 0.47/0.86  fof(f172,plain,(
% 0.47/0.86    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.47/0.86    inference(subsumption_resolution,[],[f171,f52])).
% 0.47/0.86  fof(f171,plain,(
% 0.47/0.86    k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.47/0.86    inference(subsumption_resolution,[],[f170,f50])).
% 0.47/0.86  fof(f170,plain,(
% 0.47/0.86    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.47/0.86    inference(subsumption_resolution,[],[f169,f48])).
% 0.47/0.86  fof(f48,plain,(
% 0.47/0.86    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.47/0.86    inference(cnf_transformation,[],[f21])).
% 0.47/0.86  fof(f169,plain,(
% 0.47/0.86    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.47/0.86    inference(subsumption_resolution,[],[f168,f56])).
% 0.47/0.86  fof(f168,plain,(
% 0.47/0.86    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.47/0.86    inference(subsumption_resolution,[],[f157,f54])).
% 0.47/0.86  fof(f157,plain,(
% 0.47/0.86    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.47/0.86    inference(resolution,[],[f55,f82])).
% 0.47/0.86  fof(f82,plain,(
% 0.47/0.86    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 0.47/0.86    inference(cnf_transformation,[],[f38])).
% 0.47/0.86  fof(f38,plain,(
% 0.47/0.86    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.47/0.86    inference(flattening,[],[f37])).
% 0.47/0.86  fof(f37,plain,(
% 0.47/0.86    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.47/0.86    inference(ennf_transformation,[],[f17])).
% 0.47/0.86  fof(f17,axiom,(
% 0.47/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.47/0.86  fof(f1385,plain,(
% 0.47/0.86    ( ! [X13] : (~v1_relat_1(X13) | k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X13) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X13))) )),
% 0.47/0.86    inference(resolution,[],[f256,f254])).
% 0.47/0.86  fof(f256,plain,(
% 0.47/0.86    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3))) )),
% 0.47/0.86    inference(resolution,[],[f232,f64])).
% 0.47/0.86  fof(f64,plain,(
% 0.47/0.86    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.47/0.86    inference(cnf_transformation,[],[f24])).
% 0.47/0.86  fof(f24,plain,(
% 0.47/0.86    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.47/0.86    inference(ennf_transformation,[],[f1])).
% 0.47/0.86  fof(f1,axiom,(
% 0.47/0.86    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.47/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.47/0.86  % SZS output end Proof for theBenchmark
% 0.47/0.86  % (6092)------------------------------
% 0.47/0.86  % (6092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.47/0.86  % (6092)Termination reason: Refutation
% 0.47/0.86  
% 0.47/0.86  % (6092)Memory used [KB]: 2430
% 0.47/0.86  % (6092)Time elapsed: 0.160 s
% 0.47/0.86  % (6092)------------------------------
% 0.47/0.86  % (6092)------------------------------
% 0.47/0.87  % (5905)Success in time 0.497 s
%------------------------------------------------------------------------------
