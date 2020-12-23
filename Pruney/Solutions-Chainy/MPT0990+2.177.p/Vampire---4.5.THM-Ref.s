%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:59 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  178 (5973 expanded)
%              Number of leaves         :   23 (1864 expanded)
%              Depth                    :   54
%              Number of atoms          :  773 (61414 expanded)
%              Number of equality atoms :  230 (20609 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f80,f57,f483,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f483,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f482,f466])).

fof(f466,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f465,f260])).

fof(f260,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f258,f57])).

fof(f258,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f257,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f257,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f256,f139])).

fof(f139,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f59,f136])).

fof(f136,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f135,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

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

fof(f135,plain,
    ( ~ v1_funct_1(sK2)
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f134,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f133,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f133,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f130,f57])).

fof(f130,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(resolution,[],[f95,f112])).

fof(f112,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f109,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f109,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f91,f59])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f59,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f256,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(forward_demodulation,[],[f255,f136])).

fof(f255,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f254,f55])).

fof(f254,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f253,f57])).

fof(f253,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f176,f56])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f176,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK1,sK0)
      | sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_partfun1(sK0))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f175,f52])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f173,f54])).

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_partfun1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f86,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f465,plain,
    ( k1_relat_1(sK2) = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f464,f55])).

fof(f464,plain,
    ( k1_relat_1(sK2) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f457,f246])).

fof(f246,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f245,f96])).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f65])).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f245,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f244,f136])).

fof(f244,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f243,f52])).

fof(f243,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f242,f58])).

fof(f58,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f242,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f241,f54])).

fof(f241,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f195,f53])).

fof(f195,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,X2,sK1)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f194,f55])).

fof(f194,plain,(
    ! [X2,X3] :
      ( sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f193,f57])).

fof(f193,plain,(
    ! [X2,X3] :
      ( sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f192,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f192,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f89,f56])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f457,plain,
    ( k1_relat_1(sK2) = k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f77,f433])).

fof(f433,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f430,f80])).

fof(f430,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f429,f54])).

fof(f429,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | sK2 = k2_funct_1(sK3)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f426,f80])).

fof(f426,plain,(
    ! [X0] :
      ( sK2 = k2_funct_1(sK3)
      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f423,f57])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | sK2 = k2_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f419,f74])).

fof(f419,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | sK2 = k2_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f272,f416])).

fof(f416,plain,(
    ! [X0] :
      ( sK1 = k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f415,f74])).

fof(f415,plain,(
    ! [X0] :
      ( sK1 = k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f414,f55])).

fof(f414,plain,(
    ! [X0] :
      ( sK1 = k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f412,f246])).

fof(f412,plain,(
    ! [X0] :
      ( sK1 = k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f409,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f409,plain,(
    ! [X0] :
      ( sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f408,f105])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f66,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f408,plain,(
    ! [X0] :
      ( sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f384,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f384,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f383,f260])).

fof(f383,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f382,f74])).

fof(f382,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f381,f55])).

fof(f381,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f380,f246])).

fof(f380,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f378,f77])).

fof(f378,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f377,f74])).

fof(f377,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f375,f55])).

fof(f375,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f373,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f373,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK3))
      | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0)
      | sK1 = k2_relat_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f371,f74])).

fof(f371,plain,
    ( ~ v1_relat_1(sK3)
    | sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f370,f260])).

fof(f370,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f369,f98])).

fof(f98,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f369,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(k2_funct_1(sK3))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f73,f367])).

fof(f367,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f366,f61])).

fof(f366,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f365,f57])).

fof(f365,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f364,f257])).

fof(f364,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f251,f56])).

fof(f251,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK3,X3,X2)
      | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3))
      | k2_relset_1(X3,X2,sK3) != X2
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f248,f55])).

fof(f248,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3))
      | k2_relset_1(X3,X2,sK3) != X2
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK3,X3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f246,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f272,plain,(
    ! [X0] :
      ( sK1 != k1_relat_1(sK3)
      | sK2 = k2_funct_1(sK3)
      | ~ v1_relat_1(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f271,f108])).

fof(f108,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f106,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f83,f58])).

fof(f271,plain,(
    ! [X0] :
      ( sK2 = k2_funct_1(sK3)
      | ~ v1_relat_1(sK2)
      | k2_relat_1(sK2) != k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f270,f52])).

fof(f270,plain,(
    ! [X0] :
      ( sK2 = k2_funct_1(sK3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k2_relat_1(sK2) != k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,(
    ! [X0] :
      ( k6_partfun1(sK0) != k6_partfun1(sK0)
      | sK2 = k2_funct_1(sK3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k2_relat_1(sK2) != k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f265,f165])).

fof(f165,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f164,f52])).

fof(f164,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f54])).

fof(f158,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f156,f136])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f125,f57])).

fof(f125,plain,(
    ! [X26,X24,X23,X25,X22] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_partfun1(X24,X25,X22,X23,X26,sK3) = k5_relat_1(X26,sK3)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ v1_funct_1(X26) ) ),
    inference(resolution,[],[f93,f55])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f265,plain,(
    ! [X0,X1] :
      ( k6_partfun1(sK0) != k5_relat_1(X0,sK3)
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f261,f74])).

fof(f261,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK3)
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k6_partfun1(sK0) != k5_relat_1(X4,sK3) ) ),
    inference(backward_demodulation,[],[f252,f260])).

fof(f252,plain,(
    ! [X4] :
      ( k5_relat_1(X4,sK3) != k6_partfun1(k2_relat_1(sK3))
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f249,f55])).

fof(f249,plain,(
    ! [X4] :
      ( k5_relat_1(X4,sK3) != k6_partfun1(k2_relat_1(sK3))
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f246,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f79,f65])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f77,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f482,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f481,f260])).

fof(f481,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f480,f467])).

fof(f467,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f459,f55])).

fof(f459,plain,
    ( v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f75,f433])).

fof(f480,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f479,f55])).

fof(f479,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f476,f63])).

fof(f63,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f476,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f474])).

fof(f474,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f118,f438])).

fof(f438,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f367,f433])).

fof(f118,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(sK1)
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f117,f108])).

fof(f117,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f115,f52])).

fof(f115,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f100,f60])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:49:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (28954)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (28962)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (28948)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (28941)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (28942)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (28944)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (28940)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (28939)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (28957)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (28967)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (28955)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (28943)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (28959)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (28951)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.55  % (28963)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.55  % (28950)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.55  % (28960)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.55  % (28958)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.38/0.55  % (28945)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.55  % (28949)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.55  % (28968)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.55  % (28956)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.55  % (28953)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.56  % (28952)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.56  % (28966)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.56  % (28961)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.56  % (28955)Refutation not found, incomplete strategy% (28955)------------------------------
% 1.38/0.56  % (28955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (28955)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (28955)Memory used [KB]: 10746
% 1.38/0.56  % (28955)Time elapsed: 0.147 s
% 1.38/0.56  % (28955)------------------------------
% 1.38/0.56  % (28955)------------------------------
% 1.38/0.56  % (28946)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.56  % (28964)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.56  % (28965)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.60/0.57  % (28947)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.60/0.58  % (28949)Refutation not found, incomplete strategy% (28949)------------------------------
% 1.60/0.58  % (28949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (28949)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (28949)Memory used [KB]: 11001
% 1.60/0.58  % (28949)Time elapsed: 0.144 s
% 1.60/0.58  % (28949)------------------------------
% 1.60/0.58  % (28949)------------------------------
% 1.60/0.62  % (28961)Refutation found. Thanks to Tanya!
% 1.60/0.62  % SZS status Theorem for theBenchmark
% 1.60/0.62  % SZS output start Proof for theBenchmark
% 1.60/0.62  fof(f503,plain,(
% 1.60/0.62    $false),
% 1.60/0.62    inference(unit_resulting_resolution,[],[f80,f57,f483,f74])).
% 1.60/0.62  fof(f74,plain,(
% 1.60/0.62    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f27])).
% 1.60/0.62  fof(f27,plain,(
% 1.60/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.60/0.62    inference(ennf_transformation,[],[f4])).
% 1.60/0.62  fof(f4,axiom,(
% 1.60/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.60/0.62  fof(f483,plain,(
% 1.60/0.62    ~v1_relat_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f482,f466])).
% 1.60/0.62  fof(f466,plain,(
% 1.60/0.62    sK0 = k1_relat_1(sK2) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(forward_demodulation,[],[f465,f260])).
% 1.60/0.62  fof(f260,plain,(
% 1.60/0.62    sK0 = k2_relat_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f258,f57])).
% 1.60/0.62  fof(f258,plain,(
% 1.60/0.62    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.60/0.62    inference(superposition,[],[f257,f83])).
% 1.60/0.62  fof(f83,plain,(
% 1.60/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.62    inference(cnf_transformation,[],[f34])).
% 1.60/0.62  fof(f34,plain,(
% 1.60/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.62    inference(ennf_transformation,[],[f12])).
% 1.60/0.62  fof(f12,axiom,(
% 1.60/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.60/0.62  fof(f257,plain,(
% 1.60/0.62    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f256,f139])).
% 1.60/0.62  fof(f139,plain,(
% 1.60/0.62    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.60/0.62    inference(backward_demodulation,[],[f59,f136])).
% 1.60/0.62  fof(f136,plain,(
% 1.60/0.62    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f135,f52])).
% 1.60/0.62  fof(f52,plain,(
% 1.60/0.62    v1_funct_1(sK2)),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f49,plain,(
% 1.60/0.62    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.60/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f48,f47])).
% 1.60/0.62  fof(f47,plain,(
% 1.60/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.60/0.62    introduced(choice_axiom,[])).
% 1.60/0.62  fof(f48,plain,(
% 1.60/0.62    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.60/0.62    introduced(choice_axiom,[])).
% 1.60/0.62  fof(f24,plain,(
% 1.60/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.60/0.62    inference(flattening,[],[f23])).
% 1.60/0.62  fof(f23,plain,(
% 1.60/0.62    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.60/0.62    inference(ennf_transformation,[],[f22])).
% 1.60/0.62  fof(f22,negated_conjecture,(
% 1.60/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.60/0.62    inference(negated_conjecture,[],[f21])).
% 1.60/0.62  fof(f21,conjecture,(
% 1.60/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.60/0.62  fof(f135,plain,(
% 1.60/0.62    ~v1_funct_1(sK2) | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f134,f54])).
% 1.60/0.62  fof(f54,plain,(
% 1.60/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f134,plain,(
% 1.60/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f133,f55])).
% 1.60/0.62  fof(f55,plain,(
% 1.60/0.62    v1_funct_1(sK3)),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f133,plain,(
% 1.60/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f130,f57])).
% 1.60/0.62  fof(f130,plain,(
% 1.60/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.60/0.62    inference(resolution,[],[f95,f112])).
% 1.60/0.62  fof(f112,plain,(
% 1.60/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f109,f70])).
% 1.60/0.62  fof(f70,plain,(
% 1.60/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.60/0.62    inference(cnf_transformation,[],[f15])).
% 1.60/0.62  fof(f15,axiom,(
% 1.60/0.62    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.60/0.62  fof(f109,plain,(
% 1.60/0.62    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.60/0.62    inference(resolution,[],[f91,f59])).
% 1.60/0.62  fof(f91,plain,(
% 1.60/0.62    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.62    inference(cnf_transformation,[],[f51])).
% 1.60/0.62  fof(f51,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.62    inference(nnf_transformation,[],[f42])).
% 1.60/0.62  fof(f42,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.62    inference(flattening,[],[f41])).
% 1.60/0.62  fof(f41,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.60/0.62    inference(ennf_transformation,[],[f13])).
% 1.60/0.62  fof(f13,axiom,(
% 1.60/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.60/0.62  fof(f95,plain,(
% 1.60/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f46])).
% 1.60/0.62  fof(f46,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.60/0.62    inference(flattening,[],[f45])).
% 1.60/0.62  fof(f45,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.60/0.62    inference(ennf_transformation,[],[f14])).
% 1.60/0.62  fof(f14,axiom,(
% 1.60/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.60/0.62  fof(f59,plain,(
% 1.60/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f256,plain,(
% 1.60/0.62    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.60/0.62    inference(forward_demodulation,[],[f255,f136])).
% 1.60/0.62  fof(f255,plain,(
% 1.60/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.60/0.62    inference(subsumption_resolution,[],[f254,f55])).
% 1.60/0.62  fof(f254,plain,(
% 1.60/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~v1_funct_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f253,f57])).
% 1.60/0.62  fof(f253,plain,(
% 1.60/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~v1_funct_1(sK3)),
% 1.60/0.62    inference(resolution,[],[f176,f56])).
% 1.60/0.62  fof(f56,plain,(
% 1.60/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f176,plain,(
% 1.60/0.62    ( ! [X0] : (~v1_funct_2(X0,sK1,sK0) | sK0 = k2_relset_1(sK1,sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_partfun1(sK0)) | ~v1_funct_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f175,f52])).
% 1.60/0.62  fof(f175,plain,(
% 1.60/0.62    ( ! [X0] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,X0) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f173,f54])).
% 1.60/0.62  fof(f173,plain,(
% 1.60/0.62    ( ! [X0] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK0 = k2_relset_1(sK1,sK0,X0) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.60/0.62    inference(resolution,[],[f86,f53])).
% 1.60/0.62  fof(f53,plain,(
% 1.60/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f86,plain,(
% 1.60/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) = X1 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f38])).
% 1.60/0.62  fof(f38,plain,(
% 1.60/0.62    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.62    inference(flattening,[],[f37])).
% 1.60/0.62  fof(f37,plain,(
% 1.60/0.62    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.60/0.62    inference(ennf_transformation,[],[f18])).
% 1.60/0.62  fof(f18,axiom,(
% 1.60/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.60/0.62  fof(f465,plain,(
% 1.60/0.62    k1_relat_1(sK2) = k2_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f464,f55])).
% 1.60/0.62  fof(f464,plain,(
% 1.60/0.62    k1_relat_1(sK2) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f457,f246])).
% 1.60/0.62  fof(f246,plain,(
% 1.60/0.62    v2_funct_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f245,f96])).
% 1.60/0.62  fof(f96,plain,(
% 1.60/0.62    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.60/0.62    inference(definition_unfolding,[],[f68,f65])).
% 1.60/0.62  fof(f65,plain,(
% 1.60/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f17])).
% 1.60/0.62  fof(f17,axiom,(
% 1.60/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.60/0.62  fof(f68,plain,(
% 1.60/0.62    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.60/0.62    inference(cnf_transformation,[],[f9])).
% 1.60/0.62  fof(f9,axiom,(
% 1.60/0.62    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.60/0.62  fof(f245,plain,(
% 1.60/0.62    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3)),
% 1.60/0.62    inference(forward_demodulation,[],[f244,f136])).
% 1.60/0.62  fof(f244,plain,(
% 1.60/0.62    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f243,f52])).
% 1.60/0.62  fof(f243,plain,(
% 1.60/0.62    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 1.60/0.62    inference(subsumption_resolution,[],[f242,f58])).
% 1.60/0.62  fof(f58,plain,(
% 1.60/0.62    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f242,plain,(
% 1.60/0.62    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_1(sK2)),
% 1.60/0.62    inference(subsumption_resolution,[],[f241,f54])).
% 1.60/0.62  fof(f241,plain,(
% 1.60/0.62    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_1(sK2)),
% 1.60/0.62    inference(resolution,[],[f195,f53])).
% 1.60/0.62  fof(f195,plain,(
% 1.60/0.62    ( ! [X2,X3] : (~v1_funct_2(X3,X2,sK1) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | sK1 != k2_relset_1(X2,sK1,X3) | ~v1_funct_1(X3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f194,f55])).
% 1.60/0.62  fof(f194,plain,(
% 1.60/0.62    ( ! [X2,X3] : (sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f193,f57])).
% 1.60/0.62  fof(f193,plain,(
% 1.60/0.62    ( ! [X2,X3] : (sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f192,f61])).
% 1.60/0.62  fof(f61,plain,(
% 1.60/0.62    k1_xboole_0 != sK0),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f192,plain,(
% 1.60/0.62    ( ! [X2,X3] : (k1_xboole_0 = sK0 | sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.60/0.62    inference(resolution,[],[f89,f56])).
% 1.60/0.62  fof(f89,plain,(
% 1.60/0.62    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X1,X2) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_1(X4) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f40])).
% 1.60/0.62  fof(f40,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.60/0.62    inference(flattening,[],[f39])).
% 1.60/0.62  fof(f39,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.60/0.62    inference(ennf_transformation,[],[f19])).
% 1.60/0.62  fof(f19,axiom,(
% 1.60/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.60/0.62  fof(f457,plain,(
% 1.60/0.62    k1_relat_1(sK2) = k2_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(superposition,[],[f77,f433])).
% 1.60/0.62  fof(f433,plain,(
% 1.60/0.62    sK2 = k2_funct_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f430,f80])).
% 1.60/0.62  fof(f430,plain,(
% 1.60/0.62    sK2 = k2_funct_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.60/0.62    inference(resolution,[],[f429,f54])).
% 1.60/0.62  fof(f429,plain,(
% 1.60/0.62    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | sK2 = k2_funct_1(sK3) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f426,f80])).
% 1.60/0.62  fof(f426,plain,(
% 1.60/0.62    ( ! [X0] : (sK2 = k2_funct_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(resolution,[],[f423,f57])).
% 1.60/0.62  fof(f423,plain,(
% 1.60/0.62    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | sK2 = k2_funct_1(sK3) | ~v1_relat_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 1.60/0.62    inference(resolution,[],[f419,f74])).
% 1.60/0.62  fof(f419,plain,(
% 1.60/0.62    ( ! [X0] : (~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(global_subsumption,[],[f272,f416])).
% 1.60/0.62  fof(f416,plain,(
% 1.60/0.62    ( ! [X0] : (sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f415,f74])).
% 1.60/0.62  fof(f415,plain,(
% 1.60/0.62    ( ! [X0] : (sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f414,f55])).
% 1.60/0.62  fof(f414,plain,(
% 1.60/0.62    ( ! [X0] : (sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f412,f246])).
% 1.60/0.62  fof(f412,plain,(
% 1.60/0.62    ( ! [X0] : (sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(superposition,[],[f409,f78])).
% 1.60/0.62  fof(f78,plain,(
% 1.60/0.62    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f31])).
% 1.60/0.62  fof(f31,plain,(
% 1.60/0.62    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.62    inference(flattening,[],[f30])).
% 1.60/0.62  fof(f30,plain,(
% 1.60/0.62    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.62    inference(ennf_transformation,[],[f10])).
% 1.60/0.62  fof(f10,axiom,(
% 1.60/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.60/0.62  fof(f409,plain,(
% 1.60/0.62    ( ! [X0] : (sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f408,f105])).
% 1.60/0.62  fof(f105,plain,(
% 1.60/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.60/0.62    inference(forward_demodulation,[],[f66,f64])).
% 1.60/0.62  fof(f64,plain,(
% 1.60/0.62    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.60/0.62    inference(cnf_transformation,[],[f1])).
% 1.60/0.62  fof(f1,axiom,(
% 1.60/0.62    ! [X0] : k2_subset_1(X0) = X0),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.60/0.62  fof(f66,plain,(
% 1.60/0.62    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.60/0.62    inference(cnf_transformation,[],[f2])).
% 1.60/0.62  fof(f2,axiom,(
% 1.60/0.62    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.60/0.62  fof(f408,plain,(
% 1.60/0.62    ( ! [X0] : (sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0))) )),
% 1.60/0.62    inference(resolution,[],[f384,f81])).
% 1.60/0.62  fof(f81,plain,(
% 1.60/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.60/0.62    inference(cnf_transformation,[],[f50])).
% 1.60/0.62  fof(f50,plain,(
% 1.60/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.60/0.62    inference(nnf_transformation,[],[f3])).
% 1.60/0.62  fof(f3,axiom,(
% 1.60/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.60/0.62  fof(f384,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(sK0,sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(forward_demodulation,[],[f383,f260])).
% 1.60/0.62  fof(f383,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f382,f74])).
% 1.60/0.62  fof(f382,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f381,f55])).
% 1.60/0.62  fof(f381,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f380,f246])).
% 1.60/0.62  fof(f380,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(superposition,[],[f378,f77])).
% 1.60/0.62  fof(f378,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f377,f74])).
% 1.60/0.62  fof(f377,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f375,f55])).
% 1.60/0.62  fof(f375,plain,(
% 1.60/0.62    ( ! [X0] : (~r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(resolution,[],[f373,f75])).
% 1.60/0.62  fof(f75,plain,(
% 1.60/0.62    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f29])).
% 1.60/0.62  fof(f29,plain,(
% 1.60/0.62    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.62    inference(flattening,[],[f28])).
% 1.60/0.62  fof(f28,plain,(
% 1.60/0.62    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.62    inference(ennf_transformation,[],[f8])).
% 1.60/0.62  fof(f8,axiom,(
% 1.60/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.60/0.62  fof(f373,plain,(
% 1.60/0.62    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(resolution,[],[f371,f74])).
% 1.60/0.62  fof(f371,plain,(
% 1.60/0.62    ~v1_relat_1(sK3) | sK1 = k2_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK0) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.60/0.62    inference(forward_demodulation,[],[f370,f260])).
% 1.60/0.62  fof(f370,plain,(
% 1.60/0.62    sK1 = k2_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.60/0.62    inference(forward_demodulation,[],[f369,f98])).
% 1.60/0.62  fof(f98,plain,(
% 1.60/0.62    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.60/0.62    inference(definition_unfolding,[],[f72,f65])).
% 1.60/0.62  fof(f72,plain,(
% 1.60/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.60/0.62    inference(cnf_transformation,[],[f7])).
% 1.60/0.62  fof(f7,axiom,(
% 1.60/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.60/0.62  fof(f369,plain,(
% 1.60/0.62    k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(k2_funct_1(sK3)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.60/0.62    inference(superposition,[],[f73,f367])).
% 1.60/0.62  fof(f367,plain,(
% 1.60/0.62    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.60/0.62    inference(subsumption_resolution,[],[f366,f61])).
% 1.60/0.62  fof(f366,plain,(
% 1.60/0.62    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | k1_xboole_0 = sK0),
% 1.60/0.62    inference(subsumption_resolution,[],[f365,f57])).
% 1.60/0.62  fof(f365,plain,(
% 1.60/0.62    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0),
% 1.60/0.62    inference(subsumption_resolution,[],[f364,f257])).
% 1.60/0.62  fof(f364,plain,(
% 1.60/0.62    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0),
% 1.60/0.62    inference(resolution,[],[f251,f56])).
% 1.60/0.62  fof(f251,plain,(
% 1.60/0.62    ( ! [X2,X3] : (~v1_funct_2(sK3,X3,X2) | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3)) | k2_relset_1(X3,X2,sK3) != X2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | k1_xboole_0 = X2) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f248,f55])).
% 1.60/0.62  fof(f248,plain,(
% 1.60/0.62    ( ! [X2,X3] : (k1_xboole_0 = X2 | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3)) | k2_relset_1(X3,X2,sK3) != X2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK3,X3,X2) | ~v1_funct_1(sK3)) )),
% 1.60/0.62    inference(resolution,[],[f246,f84])).
% 1.60/0.62  fof(f84,plain,(
% 1.60/0.62    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f36])).
% 1.60/0.62  fof(f36,plain,(
% 1.60/0.62    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.62    inference(flattening,[],[f35])).
% 1.60/0.62  fof(f35,plain,(
% 1.60/0.62    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.60/0.62    inference(ennf_transformation,[],[f20])).
% 1.60/0.62  fof(f20,axiom,(
% 1.60/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.60/0.62  fof(f73,plain,(
% 1.60/0.62    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f26])).
% 1.60/0.62  fof(f26,plain,(
% 1.60/0.62    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.60/0.62    inference(flattening,[],[f25])).
% 1.60/0.62  fof(f25,plain,(
% 1.60/0.62    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.60/0.62    inference(ennf_transformation,[],[f6])).
% 1.60/0.62  fof(f6,axiom,(
% 1.60/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.60/0.62  fof(f272,plain,(
% 1.60/0.62    ( ! [X0] : (sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v1_relat_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(forward_demodulation,[],[f271,f108])).
% 1.60/0.62  fof(f108,plain,(
% 1.60/0.62    sK1 = k2_relat_1(sK2)),
% 1.60/0.62    inference(subsumption_resolution,[],[f106,f54])).
% 1.60/0.62  fof(f106,plain,(
% 1.60/0.62    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.60/0.62    inference(superposition,[],[f83,f58])).
% 1.60/0.62  fof(f271,plain,(
% 1.60/0.62    ( ! [X0] : (sK2 = k2_funct_1(sK3) | ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f270,f52])).
% 1.60/0.62  fof(f270,plain,(
% 1.60/0.62    ( ! [X0] : (sK2 = k2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(trivial_inequality_removal,[],[f269])).
% 1.60/0.62  fof(f269,plain,(
% 1.60/0.62    ( ! [X0] : (k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(superposition,[],[f265,f165])).
% 1.60/0.62  fof(f165,plain,(
% 1.60/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f164,f52])).
% 1.60/0.62  fof(f164,plain,(
% 1.60/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.60/0.62    inference(subsumption_resolution,[],[f158,f54])).
% 1.60/0.62  fof(f158,plain,(
% 1.60/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.60/0.62    inference(superposition,[],[f156,f136])).
% 1.60/0.62  fof(f156,plain,(
% 1.60/0.62    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.60/0.62    inference(resolution,[],[f125,f57])).
% 1.60/0.62  fof(f125,plain,(
% 1.60/0.62    ( ! [X26,X24,X23,X25,X22] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k1_partfun1(X24,X25,X22,X23,X26,sK3) = k5_relat_1(X26,sK3) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) | ~v1_funct_1(X26)) )),
% 1.60/0.62    inference(resolution,[],[f93,f55])).
% 1.60/0.62  fof(f93,plain,(
% 1.60/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f44])).
% 1.60/0.62  fof(f44,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.60/0.62    inference(flattening,[],[f43])).
% 1.60/0.62  fof(f43,plain,(
% 1.60/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.60/0.62    inference(ennf_transformation,[],[f16])).
% 1.60/0.62  fof(f16,axiom,(
% 1.60/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.60/0.62  fof(f265,plain,(
% 1.60/0.62    ( ! [X0,X1] : (k6_partfun1(sK0) != k5_relat_1(X0,sK3) | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 1.60/0.62    inference(resolution,[],[f261,f74])).
% 1.60/0.62  fof(f261,plain,(
% 1.60/0.62    ( ! [X4] : (~v1_relat_1(sK3) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k6_partfun1(sK0) != k5_relat_1(X4,sK3)) )),
% 1.60/0.62    inference(backward_demodulation,[],[f252,f260])).
% 1.60/0.62  fof(f252,plain,(
% 1.60/0.62    ( ! [X4] : (k5_relat_1(X4,sK3) != k6_partfun1(k2_relat_1(sK3)) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f249,f55])).
% 1.60/0.62  fof(f249,plain,(
% 1.60/0.62    ( ! [X4] : (k5_relat_1(X4,sK3) != k6_partfun1(k2_relat_1(sK3)) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.60/0.62    inference(resolution,[],[f246,f100])).
% 1.60/0.62  fof(f100,plain,(
% 1.60/0.62    ( ! [X0,X1] : (~v2_funct_1(X0) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(definition_unfolding,[],[f79,f65])).
% 1.60/0.62  fof(f79,plain,(
% 1.60/0.62    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f33])).
% 1.60/0.62  fof(f33,plain,(
% 1.60/0.62    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.62    inference(flattening,[],[f32])).
% 1.60/0.62  fof(f32,plain,(
% 1.60/0.62    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.62    inference(ennf_transformation,[],[f11])).
% 1.60/0.62  fof(f11,axiom,(
% 1.60/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.60/0.62  fof(f77,plain,(
% 1.60/0.62    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.62    inference(cnf_transformation,[],[f31])).
% 1.60/0.62  fof(f482,plain,(
% 1.60/0.62    sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(forward_demodulation,[],[f481,f260])).
% 1.60/0.62  fof(f481,plain,(
% 1.60/0.62    k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f480,f467])).
% 1.60/0.62  fof(f467,plain,(
% 1.60/0.62    v1_relat_1(sK2) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(subsumption_resolution,[],[f459,f55])).
% 1.60/0.62  fof(f459,plain,(
% 1.60/0.62    v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.60/0.62    inference(superposition,[],[f75,f433])).
% 1.60/0.62  fof(f480,plain,(
% 1.60/0.62    k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.60/0.62    inference(subsumption_resolution,[],[f479,f55])).
% 1.60/0.62  fof(f479,plain,(
% 1.60/0.62    k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.60/0.62    inference(subsumption_resolution,[],[f476,f63])).
% 1.60/0.62  fof(f63,plain,(
% 1.60/0.62    k2_funct_1(sK2) != sK3),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f476,plain,(
% 1.60/0.62    k1_relat_1(sK2) != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.60/0.62    inference(trivial_inequality_removal,[],[f474])).
% 1.60/0.62  fof(f474,plain,(
% 1.60/0.62    k6_partfun1(sK1) != k6_partfun1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.60/0.62    inference(superposition,[],[f118,f438])).
% 1.60/0.62  fof(f438,plain,(
% 1.60/0.62    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 1.60/0.62    inference(backward_demodulation,[],[f367,f433])).
% 1.60/0.62  fof(f118,plain,(
% 1.60/0.62    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(sK1) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 1.60/0.62    inference(forward_demodulation,[],[f117,f108])).
% 1.60/0.62  fof(f117,plain,(
% 1.60/0.62    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 1.60/0.62    inference(subsumption_resolution,[],[f115,f52])).
% 1.60/0.62  fof(f115,plain,(
% 1.60/0.62    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.60/0.62    inference(resolution,[],[f100,f60])).
% 1.60/0.62  fof(f60,plain,(
% 1.60/0.62    v2_funct_1(sK2)),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f57,plain,(
% 1.60/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.60/0.62    inference(cnf_transformation,[],[f49])).
% 1.60/0.62  fof(f80,plain,(
% 1.60/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.60/0.62    inference(cnf_transformation,[],[f5])).
% 1.60/0.62  fof(f5,axiom,(
% 1.60/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.60/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.60/0.62  % SZS output end Proof for theBenchmark
% 1.60/0.62  % (28961)------------------------------
% 1.60/0.62  % (28961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.62  % (28961)Termination reason: Refutation
% 1.60/0.62  
% 1.60/0.62  % (28961)Memory used [KB]: 6780
% 1.60/0.62  % (28961)Time elapsed: 0.185 s
% 1.60/0.62  % (28961)------------------------------
% 1.60/0.62  % (28961)------------------------------
% 1.60/0.63  % (28938)Success in time 0.256 s
%------------------------------------------------------------------------------
