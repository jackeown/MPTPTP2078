%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 (1037 expanded)
%              Number of leaves         :   18 ( 256 expanded)
%              Depth                    :   24
%              Number of atoms          :  420 (5225 expanded)
%              Number of equality atoms :   70 ( 158 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(subsumption_resolution,[],[f467,f118])).

fof(f118,plain,(
    ! [X2] : r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2)) ),
    inference(resolution,[],[f86,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f467,plain,(
    ~ r2_relset_1(sK2,sK2,k6_relat_1(sK2),k6_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f454,f466])).

fof(f466,plain,(
    k6_relat_1(sK2) = k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f465,f227])).

fof(f227,plain,(
    k6_relat_1(sK2) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f149,f226])).

fof(f226,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f122,f224])).

fof(f224,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f223,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_partfun1(sK2))
      | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_partfun1(sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK3,sK2,sK2)
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f46])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_partfun1(sK2))
        | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_partfun1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK3,sK2,sK2)
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f223,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f220,f54])).

fof(f54,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f220,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f74,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f122,plain,(
    k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f76,f56])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f149,plain,(
    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f148,f89])).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f75,f56])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f148,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f143,f53])).

fof(f143,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f140,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f140,plain,(
    v2_funct_1(sK3) ),
    inference(resolution,[],[f138,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f138,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f137,plain,
    ( ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f134,f55])).

fof(f55,plain,(
    v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f134,plain,
    ( ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3)
    | sP1(sK2,sK3) ),
    inference(resolution,[],[f80,f56])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f44])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f465,plain,(
    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f462,f53])).

fof(f462,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f440,f56])).

fof(f440,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK2,sK2,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f434,f92])).

fof(f92,plain,(
    v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f89,f88])).

fof(f88,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK2,sK2,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3))
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f82,f335])).

fof(f335,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(backward_demodulation,[],[f280,f333])).

fof(f333,plain,(
    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f332,f53])).

fof(f332,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f331,f54])).

fof(f331,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f326,f55])).

fof(f326,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f68,f56])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f280,plain,(
    m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f279,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f279,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f278,f53])).

fof(f278,plain,
    ( sP0(sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f277,f54])).

fof(f277,plain,
    ( sP0(sK2,sK3)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f272,f55])).

fof(f272,plain,
    ( sP0(sK2,sK3)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f73,f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | sP0(X0,X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f31,f42])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f454,plain,(
    ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)),k6_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f453,f118])).

fof(f453,plain,
    ( ~ r2_relset_1(sK2,sK2,k6_relat_1(sK2),k6_relat_1(sK2))
    | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)),k6_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f345,f451])).

fof(f451,plain,(
    k6_relat_1(sK2) = k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3) ),
    inference(forward_demodulation,[],[f450,f393])).

fof(f393,plain,(
    k6_relat_1(sK2) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(backward_demodulation,[],[f147,f384])).

fof(f384,plain,(
    k6_relat_1(sK2) = k6_relat_1(k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f237,f383])).

fof(f383,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f358,f369])).

fof(f369,plain,(
    sK2 = k1_relset_1(sK2,sK2,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f368,f92])).

fof(f368,plain,
    ( sK2 = k1_relset_1(sK2,sK2,k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f363,f337])).

fof(f337,plain,(
    v1_funct_2(k2_funct_1(sK3),sK2,sK2) ),
    inference(backward_demodulation,[],[f282,f333])).

fof(f282,plain,(
    v1_funct_2(k2_funct_2(sK2,sK3),sK2,sK2) ),
    inference(resolution,[],[f279,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_funct_2(k2_funct_2(X0,X1),X0,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f363,plain,
    ( sK2 = k1_relset_1(sK2,sK2,k2_funct_1(sK3))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK2)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f335,f74])).

fof(f358,plain,(
    k1_relat_1(k2_funct_1(sK3)) = k1_relset_1(sK2,sK2,k2_funct_1(sK3)) ),
    inference(resolution,[],[f335,f76])).

fof(f237,plain,(
    k6_relat_1(k2_relat_1(sK3)) = k6_relat_1(k1_relat_1(k2_funct_1(sK3))) ),
    inference(forward_demodulation,[],[f236,f147])).

fof(f236,plain,(
    k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k1_relat_1(k2_funct_1(sK3))) ),
    inference(forward_demodulation,[],[f161,f151])).

fof(f151,plain,(
    sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f150,f89])).

fof(f150,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f144,f53])).

fof(f144,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f140,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f161,plain,(
    k5_relat_1(k2_funct_1(sK3),k2_funct_1(k2_funct_1(sK3))) = k6_relat_1(k1_relat_1(k2_funct_1(sK3))) ),
    inference(subsumption_resolution,[],[f160,f93])).

fof(f93,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f89,f87])).

fof(f87,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f160,plain,
    ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(k2_funct_1(sK3))) = k6_relat_1(k1_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f155,f92])).

fof(f155,plain,
    ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(k2_funct_1(sK3))) = k6_relat_1(k1_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f153,f65])).

fof(f153,plain,(
    v2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f152,f89])).

fof(f152,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f145,f53])).

fof(f145,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f140,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f147,plain,(
    k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f146,f89])).

fof(f146,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f142,f53])).

fof(f142,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f140,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f450,plain,(
    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f444,f92])).

fof(f444,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f441,f335])).

fof(f441,plain,(
    ! [X14,X15,X13] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_partfun1(X13,X14,sK2,sK2,X15,sK3) = k5_relat_1(X15,sK3)
      | ~ v1_funct_1(X15) ) ),
    inference(subsumption_resolution,[],[f438,f53])).

fof(f438,plain,(
    ! [X14,X15,X13] :
      ( k1_partfun1(X13,X14,sK2,sK2,X15,sK3) = k5_relat_1(X15,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v1_funct_1(X15) ) ),
    inference(resolution,[],[f82,f56])).

fof(f345,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3),k6_relat_1(sK2))
    | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)),k6_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f334,f333])).

fof(f334,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3),k6_relat_1(sK2))
    | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f83,f333])).

fof(f83,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_relat_1(sK2))
    | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_relat_1(sK2)) ),
    inference(definition_unfolding,[],[f57,f58,f58])).

fof(f57,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_partfun1(sK2))
    | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (25335)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (25337)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (25346)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (25347)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (25345)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (25346)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (25338)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (25334)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (25339)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f468,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f467,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X2] : (r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2))) )),
% 0.21/0.49    inference(resolution,[],[f86,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f60,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.21/0.49    inference(condensation,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.49  fof(f467,plain,(
% 0.21/0.49    ~r2_relset_1(sK2,sK2,k6_relat_1(sK2),k6_relat_1(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f454,f466])).
% 0.21/0.49  fof(f466,plain,(
% 0.21/0.49    k6_relat_1(sK2) = k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3))),
% 0.21/0.49    inference(forward_demodulation,[],[f465,f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    k6_relat_1(sK2) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 0.21/0.49    inference(forward_demodulation,[],[f149,f226])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    sK2 = k1_relat_1(sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f122,f224])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    sK2 = k1_relset_1(sK2,sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f223,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_partfun1(sK2)) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_partfun1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_partfun1(sK2)) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_partfun1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f220,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK2,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f74,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f76,f56])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f148,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f75,f56])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f143,f53])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f140,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    v2_funct_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f138,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | v2_funct_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 0.21/0.49    inference(rectify,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    sP1(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f137,f53])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f134,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v3_funct_2(sK3,sK2,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3) | sP1(sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f80,f56])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP1(X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(definition_folding,[],[f37,f44])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.49  fof(f465,plain,(
% 0.21/0.49    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f462,f53])).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f440,f56])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK2,sK2,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3)) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f434,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f89,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f62,f53])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK2,sK2,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(resolution,[],[f82,f335])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.49    inference(backward_demodulation,[],[f280,f333])).
% 0.21/0.49  fof(f333,plain,(
% 0.21/0.49    k2_funct_2(sK2,sK3) = k2_funct_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f332,f53])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f331,f54])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f326,f55])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    k2_funct_2(sK2,sK3) = k2_funct_1(sK3) | ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f68,f56])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.49    inference(resolution,[],[f279,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    sP0(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f278,f53])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    sP0(sK2,sK3) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f277,f54])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    sP0(sK2,sK3) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f272,f55])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    sP0(sK2,sK3) | ~v3_funct_2(sK3,sK2,sK2) | ~v1_funct_2(sK3,sK2,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f73,f56])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | sP0(X0,X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.49    inference(definition_folding,[],[f31,f42])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.49    inference(flattening,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.49  fof(f454,plain,(
% 0.21/0.49    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)),k6_relat_1(sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f453,f118])).
% 0.21/0.49  fof(f453,plain,(
% 0.21/0.49    ~r2_relset_1(sK2,sK2,k6_relat_1(sK2),k6_relat_1(sK2)) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)),k6_relat_1(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f345,f451])).
% 0.21/0.49  fof(f451,plain,(
% 0.21/0.49    k6_relat_1(sK2) = k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3)),
% 0.21/0.49    inference(forward_demodulation,[],[f450,f393])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    k6_relat_1(sK2) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f147,f384])).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    k6_relat_1(sK2) = k6_relat_1(k2_relat_1(sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f237,f383])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(forward_demodulation,[],[f358,f369])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    sK2 = k1_relset_1(sK2,sK2,k2_funct_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f368,f92])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    sK2 = k1_relset_1(sK2,sK2,k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f363,f337])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    v1_funct_2(k2_funct_1(sK3),sK2,sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f282,f333])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    v1_funct_2(k2_funct_2(sK2,sK3),sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f279,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | v1_funct_2(k2_funct_2(X0,X1),X0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    sK2 = k1_relset_1(sK2,sK2,k2_funct_1(sK3)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK2) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f335,f74])).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    k1_relat_1(k2_funct_1(sK3)) = k1_relset_1(sK2,sK2,k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f335,f76])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    k6_relat_1(k2_relat_1(sK3)) = k6_relat_1(k1_relat_1(k2_funct_1(sK3)))),
% 0.21/0.49    inference(forward_demodulation,[],[f236,f147])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k1_relat_1(k2_funct_1(sK3)))),
% 0.21/0.49    inference(forward_demodulation,[],[f161,f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    sK3 = k2_funct_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f150,f89])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f144,f53])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f140,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),k2_funct_1(k2_funct_1(sK3))) = k6_relat_1(k1_relat_1(k2_funct_1(sK3)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f160,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f89,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f61,f53])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),k2_funct_1(k2_funct_1(sK3))) = k6_relat_1(k1_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f155,f92])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),k2_funct_1(k2_funct_1(sK3))) = k6_relat_1(k1_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f153,f65])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    v2_funct_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f89])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f145,f53])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f140,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k2_relat_1(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f146,f89])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f142,f53])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),sK3) = k6_relat_1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f140,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f450,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f444,f92])).
% 0.21/0.49  fof(f444,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f441,f335])).
% 0.21/0.49  fof(f441,plain,(
% 0.21/0.49    ( ! [X14,X15,X13] : (~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | k1_partfun1(X13,X14,sK2,sK2,X15,sK3) = k5_relat_1(X15,sK3) | ~v1_funct_1(X15)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f438,f53])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    ( ! [X14,X15,X13] : (k1_partfun1(X13,X14,sK2,sK2,X15,sK3) = k5_relat_1(X15,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_funct_1(X15)) )),
% 0.21/0.49    inference(resolution,[],[f82,f56])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3),k6_relat_1(sK2)) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_1(sK3)),k6_relat_1(sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f334,f333])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_1(sK3),sK3),k6_relat_1(sK2)) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_relat_1(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f83,f333])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_relat_1(sK2)) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_relat_1(sK2))),
% 0.21/0.49    inference(definition_unfolding,[],[f57,f58,f58])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k2_funct_2(sK2,sK3),sK3),k6_partfun1(sK2)) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,k2_funct_2(sK2,sK3)),k6_partfun1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (25346)------------------------------
% 0.21/0.49  % (25346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25346)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (25346)Memory used [KB]: 1791
% 0.21/0.49  % (25346)Time elapsed: 0.069 s
% 0.21/0.49  % (25346)------------------------------
% 0.21/0.49  % (25346)------------------------------
% 0.21/0.49  % (25333)Success in time 0.124 s
%------------------------------------------------------------------------------
