%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:26 EST 2020

% Result     : Theorem 55.36s
% Output     : Refutation 55.36s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 972 expanded)
%              Number of leaves         :   25 ( 191 expanded)
%              Depth                    :   31
%              Number of atoms          :  729 (5085 expanded)
%              Number of equality atoms :  100 ( 289 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38621,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f411,f1010,f38233,f38451])).

fof(f38451,plain,(
    ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f38450])).

fof(f38450,plain,
    ( $false
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f38239,f144])).

fof(f144,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f118,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f38239,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f59,f1009])).

fof(f1009,plain,
    ( sK2 = k6_partfun1(sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1007,plain,
    ( spl6_28
  <=> sK2 = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f59,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f38233,plain,
    ( spl6_3
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f38232])).

fof(f38232,plain,
    ( $false
    | spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f38231,f8819])).

fof(f8819,plain,(
    v1_funct_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f8818,f201])).

fof(f201,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f199,f62])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f199,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f172,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f171,f60])).

fof(f60,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f171,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f163,f61])).

fof(f61,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f163,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f74,f62])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f8818,plain,(
    v1_funct_1(k6_partfun1(k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f8817,f128])).

fof(f128,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f83,f62])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f8817,plain,
    ( v1_funct_1(k6_partfun1(k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f8816,f58])).

fof(f58,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f8816,plain,
    ( v1_funct_1(k6_partfun1(k1_relat_1(sK1)))
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f8815,f60])).

fof(f8815,plain,
    ( v1_funct_1(k6_partfun1(k1_relat_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f8579,f112])).

fof(f112,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f72,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f8579,plain,(
    v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f8556,f1875])).

fof(f1875,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f1874,f60])).

fof(f1874,plain,
    ( ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f1873,f58])).

fof(f1873,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f1860,f218])).

fof(f218,plain,(
    v1_funct_2(sK1,sK0,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f217,f128])).

fof(f217,plain,
    ( v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f214,f60])).

fof(f214,plain,
    ( v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f70,f201])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1860,plain,
    ( ~ v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f791,f216])).

fof(f216,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f215,f128])).

fof(f215,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f213,f60])).

fof(f213,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f71,f201])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f791,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
      | ~ v1_funct_2(X0,X1,k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f88,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f8556,plain,
    ( v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f8537,f1854])).

fof(f1854,plain,(
    ! [X39,X38,X40] :
      ( ~ r1_tarski(X38,k2_zfmisc_1(X39,X40))
      | v1_funct_1(k5_relat_1(sK1,X38))
      | ~ v1_funct_1(X38) ) ),
    inference(subsumption_resolution,[],[f1842,f60])).

fof(f1842,plain,(
    ! [X39,X38,X40] :
      ( ~ v1_funct_1(X38)
      | v1_funct_1(k5_relat_1(sK1,X38))
      | ~ v1_funct_1(sK1)
      | ~ r1_tarski(X38,k2_zfmisc_1(X39,X40)) ) ),
    inference(resolution,[],[f778,f62])).

fof(f778,plain,(
    ! [X66,X64,X62,X67,X65,X63] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
      | ~ v1_funct_1(X65)
      | v1_funct_1(k5_relat_1(X62,X65))
      | ~ v1_funct_1(X62)
      | ~ r1_tarski(X65,k2_zfmisc_1(X66,X67)) ) ),
    inference(resolution,[],[f270,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f270,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | v1_funct_1(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f103,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f8537,plain,(
    r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f8536,f218])).

fof(f8536,plain,
    ( ~ v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f8535,f60])).

fof(f8535,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f8516,f58])).

fof(f8516,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f2133,f216])).

fof(f2133,plain,(
    ! [X64,X63] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X64,k2_relat_1(X63))))
      | ~ v2_funct_1(X63)
      | ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,X64,k2_relat_1(X63))
      | r1_tarski(k2_funct_1(X63),k2_zfmisc_1(k2_relat_1(X63),X64)) ) ),
    inference(resolution,[],[f907,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f907,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f258])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f90,f85])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f38231,plain,
    ( ~ v1_funct_1(k6_partfun1(sK0))
    | spl6_3
    | spl6_27 ),
    inference(resolution,[],[f38230,f139])).

fof(f139,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),X0,X0)
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f138,f109])).

fof(f109,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f69,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f138,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0)))
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f136,f108])).

fof(f108,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f136,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0)))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f70,f110])).

fof(f110,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f68,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f38230,plain,
    ( ~ v1_funct_2(k6_partfun1(sK0),sK0,sK0)
    | spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f38229,f62])).

fof(f38229,plain,
    ( ~ v1_funct_2(k6_partfun1(sK0),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f38228,f1005])).

fof(f1005,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1003,plain,
    ( spl6_27
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f38228,plain,
    ( ~ v1_funct_2(k6_partfun1(sK0),sK0,sK0)
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_3 ),
    inference(subsumption_resolution,[],[f38227,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f38227,plain,
    ( ~ v1_funct_2(k6_partfun1(sK0),sK0,sK0)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_3 ),
    inference(subsumption_resolution,[],[f38217,f8819])).

fof(f38217,plain,
    ( ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(k6_partfun1(sK0),sK0,sK0)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_3 ),
    inference(resolution,[],[f2066,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f196,f67])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f86,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f2066,plain,
    ( ! [X1] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,X1,sK2) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f2065,f58])).

fof(f2065,plain,
    ( ! [X1] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ v2_funct_1(sK1) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f2064,f60])).

fof(f2064,plain,
    ( ! [X1] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK1)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ v2_funct_1(sK1) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f2063,f56])).

fof(f2063,plain,
    ( ! [X1] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK1)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ v2_funct_1(sK1) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f2062,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f2062,plain,
    ( ! [X1] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK1)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ v2_funct_1(sK1) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f2061,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f2061,plain,
    ( ! [X1] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK1)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ v2_funct_1(sK1) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f2060,f359])).

fof(f359,plain,
    ( k1_xboole_0 != sK0
    | spl6_3 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2060,plain,(
    ! [X1] :
      ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
      | k1_xboole_0 = sK0
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK1)
      | r2_relset_1(sK0,sK0,X1,sK2)
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f2059,f62])).

fof(f2059,plain,(
    ! [X1] :
      ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k1_xboole_0 = sK0
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK1)
      | r2_relset_1(sK0,sK0,X1,sK2)
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f2056,f61])).

fof(f2056,plain,(
    ! [X1] :
      ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k1_xboole_0 = sK0
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK1)
      | r2_relset_1(sK0,sK0,X1,sK2)
      | ~ v2_funct_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f2049])).

fof(f2049,plain,(
    ! [X1] :
      ( ~ r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK1)
      | r2_relset_1(sK0,sK0,X1,sK2)
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f347,f1968])).

fof(f1968,plain,(
    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f1967,f54])).

fof(f1967,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1966,f62])).

fof(f1966,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1965,f60])).

fof(f1965,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1962,f56])).

fof(f1962,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f529,f57])).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f529,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X4,X5,sK0,X6,X7),sK1)
      | sK1 = k1_partfun1(sK0,X4,X5,sK0,X6,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK0)))
      | ~ v1_funct_1(X6) ) ),
    inference(resolution,[],[f184,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f184,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | sK1 = X1
      | ~ r2_relset_1(sK0,sK0,X1,sK1) ) ),
    inference(resolution,[],[f101,f62])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f347,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | r2_relset_1(X0,X1,X3,X5)
      | ~ v2_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | r2_relset_1(X0,X1,X3,X5)
      | ~ v2_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f96,f102])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_1(X2)
      | r2_relset_1(X3,X0,X4,X5)
      | ~ v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ ( v2_funct_1(X2)
            <=> ! [X3,X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                    & v1_funct_2(X4,X3,X0)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                        & v1_funct_2(X5,X3,X0)
                        & v1_funct_1(X5) )
                     => ( r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                       => r2_relset_1(X3,X0,X4,X5) ) ) ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).

fof(f1010,plain,
    ( ~ spl6_27
    | spl6_28 ),
    inference(avatar_split_clause,[],[f514,f1007,f1003])).

fof(f514,plain,
    ( sK2 = k6_partfun1(sK0)
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2) ),
    inference(resolution,[],[f183,f67])).

fof(f183,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | sK2 = X0
      | ~ r2_relset_1(sK0,sK0,X0,sK2) ) ),
    inference(resolution,[],[f101,f56])).

fof(f411,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f408,f147])).

fof(f147,plain,(
    ! [X2,X1] : r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f118,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f408,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f395,f402])).

fof(f402,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f401,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f401,plain,
    ( sK2 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f400,f360])).

fof(f360,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f358])).

fof(f400,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f399,f121])).

fof(f121,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f79,f63])).

fof(f399,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK0)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f375,f115])).

fof(f375,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f135,f360])).

fof(f135,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK0) ),
    inference(resolution,[],[f77,f123])).

fof(f123,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f79,f56])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f395,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f370,f254])).

fof(f254,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f253,f121])).

fof(f253,plain,
    ( ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f126,f77])).

fof(f126,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f79,f119])).

fof(f119,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f67,f115])).

fof(f370,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k6_partfun1(k1_xboole_0))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f59,f360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (12965)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (12972)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (12981)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (12973)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (12966)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (12989)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12963)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (12964)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (12962)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (12960)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (12959)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (12987)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (12961)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (12967)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (12968)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (12988)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (12986)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (12975)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (12980)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (12985)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (12978)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (12982)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (12977)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (12984)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (12971)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (12970)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (12974)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (12979)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (12969)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.57/0.57  % (12976)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.57/0.57  % (12975)Refutation not found, incomplete strategy% (12975)------------------------------
% 1.57/0.57  % (12975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (12975)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (12975)Memory used [KB]: 10874
% 1.57/0.57  % (12975)Time elapsed: 0.140 s
% 1.57/0.57  % (12975)------------------------------
% 1.57/0.57  % (12975)------------------------------
% 2.10/0.68  % (12969)Refutation not found, incomplete strategy% (12969)------------------------------
% 2.10/0.68  % (12969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.68  % (12969)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.68  
% 2.10/0.68  % (12969)Memory used [KB]: 11641
% 2.10/0.68  % (12969)Time elapsed: 0.247 s
% 2.10/0.68  % (12969)------------------------------
% 2.10/0.68  % (12969)------------------------------
% 2.10/0.71  % (13004)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.69/0.71  % (12959)Refutation not found, incomplete strategy% (12959)------------------------------
% 2.69/0.71  % (12959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.71  % (12959)Termination reason: Refutation not found, incomplete strategy
% 2.69/0.71  
% 2.69/0.71  % (12959)Memory used [KB]: 1791
% 2.69/0.71  % (12959)Time elapsed: 0.272 s
% 2.69/0.71  % (12959)------------------------------
% 2.69/0.71  % (12959)------------------------------
% 3.10/0.82  % (13011)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.10/0.82  % (12984)Time limit reached!
% 3.10/0.82  % (12984)------------------------------
% 3.10/0.82  % (12984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.82  % (12984)Termination reason: Time limit
% 3.10/0.82  
% 3.10/0.82  % (12984)Memory used [KB]: 13432
% 3.10/0.82  % (12984)Time elapsed: 0.408 s
% 3.10/0.82  % (12984)------------------------------
% 3.10/0.82  % (12984)------------------------------
% 3.10/0.83  % (12961)Time limit reached!
% 3.10/0.83  % (12961)------------------------------
% 3.10/0.83  % (12961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.83  % (12961)Termination reason: Time limit
% 3.10/0.83  
% 3.10/0.83  % (12961)Memory used [KB]: 6780
% 3.10/0.83  % (12961)Time elapsed: 0.406 s
% 3.10/0.83  % (12961)------------------------------
% 3.10/0.83  % (12961)------------------------------
% 3.10/0.84  % (13012)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.10/0.85  % (12988)Refutation not found, incomplete strategy% (12988)------------------------------
% 3.10/0.85  % (12988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.85  % (12988)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.85  
% 3.10/0.85  % (12988)Memory used [KB]: 12792
% 3.10/0.85  % (12988)Time elapsed: 0.416 s
% 3.10/0.85  % (12988)------------------------------
% 3.10/0.85  % (12988)------------------------------
% 3.76/0.86  % (13012)Refutation not found, incomplete strategy% (13012)------------------------------
% 3.76/0.86  % (13012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.76/0.86  % (13012)Termination reason: Refutation not found, incomplete strategy
% 3.76/0.86  
% 3.76/0.86  % (13012)Memory used [KB]: 6268
% 3.76/0.86  % (13012)Time elapsed: 0.109 s
% 3.76/0.86  % (13012)------------------------------
% 3.76/0.86  % (13012)------------------------------
% 3.98/0.92  % (12989)Time limit reached!
% 3.98/0.92  % (12989)------------------------------
% 3.98/0.92  % (12989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (12989)Termination reason: Time limit
% 3.98/0.92  
% 3.98/0.92  % (12989)Memory used [KB]: 5500
% 3.98/0.92  % (12989)Time elapsed: 0.505 s
% 3.98/0.92  % (12989)------------------------------
% 3.98/0.92  % (12989)------------------------------
% 4.24/0.93  % (12965)Time limit reached!
% 4.24/0.93  % (12965)------------------------------
% 4.24/0.93  % (12965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.94  % (12965)Termination reason: Time limit
% 4.32/0.94  
% 4.32/0.94  % (12965)Memory used [KB]: 16375
% 4.32/0.94  % (12965)Time elapsed: 0.504 s
% 4.32/0.94  % (12965)------------------------------
% 4.32/0.94  % (12965)------------------------------
% 4.32/0.95  % (13014)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.32/0.96  % (13013)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.32/0.97  % (12973)Time limit reached!
% 4.32/0.97  % (12973)------------------------------
% 4.32/0.97  % (12973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.97  % (12973)Termination reason: Time limit
% 4.32/0.97  % (12973)Termination phase: Saturation
% 4.32/0.97  
% 4.32/0.97  % (12973)Memory used [KB]: 6012
% 4.32/0.97  % (12973)Time elapsed: 0.500 s
% 4.32/0.97  % (12973)------------------------------
% 4.32/0.97  % (12973)------------------------------
% 4.32/0.98  % (13015)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.32/0.99  % (13016)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.72/1.06  % (13017)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.72/1.06  % (12966)Time limit reached!
% 4.72/1.06  % (12966)------------------------------
% 4.72/1.06  % (12966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.06  % (12966)Termination reason: Time limit
% 4.72/1.06  
% 4.72/1.06  % (12966)Memory used [KB]: 6140
% 4.72/1.06  % (12966)Time elapsed: 0.607 s
% 4.72/1.06  % (12966)------------------------------
% 4.72/1.06  % (12966)------------------------------
% 4.72/1.07  % (13018)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.56/1.09  % (13019)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.79/1.24  % (12960)Time limit reached!
% 6.79/1.24  % (12960)------------------------------
% 6.79/1.24  % (12960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.79/1.24  % (12960)Termination reason: Time limit
% 6.79/1.24  % (12960)Termination phase: Saturation
% 6.79/1.24  
% 6.79/1.24  % (12960)Memory used [KB]: 6524
% 6.79/1.24  % (12960)Time elapsed: 0.800 s
% 6.79/1.24  % (12960)------------------------------
% 6.79/1.24  % (12960)------------------------------
% 6.79/1.24  % (13020)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 7.37/1.32  % (12962)Time limit reached!
% 7.37/1.32  % (12962)------------------------------
% 7.37/1.32  % (12962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.37/1.32  % (12962)Termination reason: Time limit
% 7.37/1.32  
% 7.37/1.32  % (12962)Memory used [KB]: 7419
% 7.37/1.32  % (12962)Time elapsed: 0.904 s
% 7.37/1.32  % (12962)------------------------------
% 7.37/1.32  % (12962)------------------------------
% 7.87/1.37  % (13021)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 7.87/1.43  % (12987)Time limit reached!
% 7.87/1.43  % (12987)------------------------------
% 7.87/1.43  % (12987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.43  % (12987)Termination reason: Time limit
% 7.87/1.43  
% 7.87/1.43  % (12987)Memory used [KB]: 13688
% 7.87/1.43  % (12987)Time elapsed: 1.021 s
% 7.87/1.43  % (12987)------------------------------
% 7.87/1.43  % (12987)------------------------------
% 7.87/1.46  % (12971)Time limit reached!
% 7.87/1.46  % (12971)------------------------------
% 7.87/1.46  % (12971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.46  % (12971)Termination reason: Time limit
% 7.87/1.46  
% 7.87/1.46  % (12971)Memory used [KB]: 16886
% 7.87/1.46  % (12971)Time elapsed: 1.023 s
% 7.87/1.46  % (12971)------------------------------
% 7.87/1.46  % (12971)------------------------------
% 8.60/1.47  % (13022)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 8.80/1.51  % (13016)Time limit reached!
% 8.80/1.51  % (13016)------------------------------
% 8.80/1.51  % (13016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.80/1.51  % (13016)Termination reason: Time limit
% 8.80/1.51  
% 8.80/1.51  % (13016)Memory used [KB]: 17526
% 8.80/1.51  % (13016)Time elapsed: 0.621 s
% 8.80/1.51  % (13016)------------------------------
% 8.80/1.51  % (13016)------------------------------
% 9.04/1.57  % (13023)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.04/1.60  % (13024)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 9.82/1.64  % (13025)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 10.35/1.73  % (12964)Time limit reached!
% 10.35/1.73  % (12964)------------------------------
% 10.35/1.73  % (12964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.73  % (12964)Termination reason: Time limit
% 10.35/1.73  
% 10.35/1.73  % (12964)Memory used [KB]: 9722
% 10.35/1.73  % (12964)Time elapsed: 1.316 s
% 10.35/1.73  % (12964)------------------------------
% 10.35/1.73  % (12964)------------------------------
% 11.48/1.85  % (13023)Time limit reached!
% 11.48/1.85  % (13023)------------------------------
% 11.48/1.85  % (13023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.48/1.85  % (13023)Termination reason: Time limit
% 11.48/1.85  % (13023)Termination phase: Saturation
% 11.48/1.85  
% 11.48/1.85  % (13023)Memory used [KB]: 13816
% 11.48/1.85  % (13023)Time elapsed: 0.400 s
% 11.48/1.85  % (13023)------------------------------
% 11.48/1.85  % (13023)------------------------------
% 11.48/1.87  % (13026)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 11.48/1.88  % (13019)Time limit reached!
% 11.48/1.88  % (13019)------------------------------
% 11.48/1.88  % (13019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.48/1.88  % (13019)Termination reason: Time limit
% 11.48/1.88  % (13019)Termination phase: Saturation
% 11.48/1.88  
% 11.48/1.88  % (13019)Memory used [KB]: 16886
% 11.48/1.88  % (13019)Time elapsed: 0.800 s
% 11.48/1.88  % (13019)------------------------------
% 11.48/1.88  % (13019)------------------------------
% 12.15/1.92  % (13025)Time limit reached!
% 12.15/1.92  % (13025)------------------------------
% 12.15/1.92  % (13025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.15/1.92  % (13025)Termination reason: Time limit
% 12.15/1.92  % (13025)Termination phase: Saturation
% 12.15/1.92  
% 12.15/1.92  % (13025)Memory used [KB]: 6780
% 12.15/1.92  % (13025)Time elapsed: 0.400 s
% 12.15/1.92  % (13025)------------------------------
% 12.15/1.92  % (13025)------------------------------
% 12.69/2.00  % (13027)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 12.69/2.01  % (12986)Time limit reached!
% 12.69/2.01  % (12986)------------------------------
% 12.69/2.01  % (12986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.69/2.01  % (12986)Termination reason: Time limit
% 12.69/2.01  % (12986)Termination phase: Saturation
% 12.69/2.01  
% 12.69/2.01  % (12986)Memory used [KB]: 13944
% 12.69/2.01  % (12986)Time elapsed: 1.600 s
% 12.69/2.01  % (12986)------------------------------
% 12.69/2.01  % (12986)------------------------------
% 12.69/2.02  % (13028)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 12.69/2.04  % (13024)Refutation not found, incomplete strategy% (13024)------------------------------
% 12.69/2.04  % (13024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.69/2.04  % (13024)Termination reason: Refutation not found, incomplete strategy
% 12.69/2.04  
% 12.69/2.04  % (13024)Memory used [KB]: 7164
% 12.69/2.04  % (13024)Time elapsed: 0.535 s
% 12.69/2.04  % (13024)------------------------------
% 12.69/2.04  % (13024)------------------------------
% 12.69/2.06  % (13029)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 13.94/2.15  % (13030)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 14.60/2.26  % (13026)Time limit reached!
% 14.60/2.26  % (13026)------------------------------
% 14.60/2.26  % (13026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.60/2.26  % (13026)Termination reason: Time limit
% 14.60/2.26  
% 14.60/2.26  % (13026)Memory used [KB]: 12665
% 14.60/2.26  % (13026)Time elapsed: 0.511 s
% 14.60/2.26  % (13026)------------------------------
% 14.60/2.26  % (13026)------------------------------
% 14.60/2.28  % (13027)Time limit reached!
% 14.60/2.28  % (13027)------------------------------
% 14.60/2.28  % (13027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.60/2.28  % (13027)Termination reason: Time limit
% 14.60/2.28  
% 14.60/2.28  % (13027)Memory used [KB]: 8571
% 14.60/2.28  % (13027)Time elapsed: 0.408 s
% 14.60/2.28  % (13027)------------------------------
% 14.60/2.28  % (13027)------------------------------
% 15.25/2.37  % (13029)Time limit reached!
% 15.25/2.37  % (13029)------------------------------
% 15.25/2.37  % (13029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.25/2.37  % (13029)Termination reason: Time limit
% 15.25/2.37  
% 15.25/2.37  % (13029)Memory used [KB]: 4477
% 15.25/2.37  % (13029)Time elapsed: 0.420 s
% 15.25/2.37  % (13029)------------------------------
% 15.25/2.37  % (13029)------------------------------
% 16.31/2.43  % (13030)Time limit reached!
% 16.31/2.43  % (13030)------------------------------
% 16.31/2.43  % (13030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.31/2.43  % (13030)Termination reason: Time limit
% 16.31/2.43  
% 16.31/2.43  % (13030)Memory used [KB]: 6780
% 16.31/2.43  % (13030)Time elapsed: 0.401 s
% 16.31/2.43  % (13030)------------------------------
% 16.31/2.43  % (13030)------------------------------
% 18.44/2.70  % (12979)Time limit reached!
% 18.44/2.70  % (12979)------------------------------
% 18.44/2.70  % (12979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.44/2.70  % (12979)Termination reason: Time limit
% 18.44/2.70  % (12979)Termination phase: Saturation
% 18.44/2.70  
% 18.44/2.70  % (12979)Memory used [KB]: 36204
% 18.44/2.70  % (12979)Time elapsed: 1.800 s
% 18.44/2.70  % (12979)------------------------------
% 18.44/2.70  % (12979)------------------------------
% 18.75/2.82  % (12974)Time limit reached!
% 18.75/2.82  % (12974)------------------------------
% 18.75/2.82  % (12974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.75/2.82  % (12974)Termination reason: Time limit
% 18.75/2.82  % (12974)Termination phase: Saturation
% 18.75/2.82  
% 18.75/2.82  % (12974)Memory used [KB]: 14328
% 18.75/2.82  % (12974)Time elapsed: 2.400 s
% 18.75/2.82  % (12974)------------------------------
% 18.75/2.82  % (12974)------------------------------
% 25.54/3.59  % (12970)Time limit reached!
% 25.54/3.59  % (12970)------------------------------
% 25.54/3.59  % (12970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.54/3.59  % (12970)Termination reason: Time limit
% 25.54/3.59  
% 25.54/3.59  % (12970)Memory used [KB]: 31470
% 25.54/3.59  % (12970)Time elapsed: 3.135 s
% 25.54/3.59  % (12970)------------------------------
% 25.54/3.59  % (12970)------------------------------
% 25.54/3.60  % (12967)Time limit reached!
% 25.54/3.60  % (12967)------------------------------
% 25.54/3.60  % (12967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.54/3.60  % (12967)Termination reason: Time limit
% 25.54/3.60  
% 25.54/3.60  % (12967)Memory used [KB]: 13816
% 25.54/3.60  % (12967)Time elapsed: 3.161 s
% 25.54/3.60  % (12967)------------------------------
% 25.54/3.60  % (12967)------------------------------
% 26.75/3.75  % (12978)Time limit reached!
% 26.75/3.75  % (12978)------------------------------
% 26.75/3.75  % (12978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.75/3.75  % (12978)Termination reason: Time limit
% 26.75/3.75  % (12978)Termination phase: Saturation
% 26.75/3.75  
% 26.75/3.75  % (12978)Memory used [KB]: 31982
% 26.75/3.75  % (12978)Time elapsed: 3.300 s
% 26.75/3.75  % (12978)------------------------------
% 26.75/3.75  % (12978)------------------------------
% 28.48/3.96  % (13018)Time limit reached!
% 28.48/3.96  % (13018)------------------------------
% 28.48/3.96  % (13018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.48/3.96  % (13018)Termination reason: Time limit
% 28.48/3.96  % (13018)Termination phase: Saturation
% 28.48/3.96  
% 28.48/3.96  % (13018)Memory used [KB]: 28912
% 28.48/3.96  % (13018)Time elapsed: 3.0000 s
% 28.48/3.96  % (13018)------------------------------
% 28.48/3.96  % (13018)------------------------------
% 30.83/4.25  % (13017)Time limit reached!
% 30.83/4.25  % (13017)------------------------------
% 30.83/4.25  % (13017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.83/4.25  % (13013)Time limit reached!
% 30.83/4.25  % (13013)------------------------------
% 30.83/4.25  % (13013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.83/4.25  % (13013)Termination reason: Time limit
% 30.83/4.25  % (13013)Termination phase: Saturation
% 30.83/4.25  
% 30.83/4.25  % (13013)Memory used [KB]: 37995
% 30.83/4.25  % (13013)Time elapsed: 3.400 s
% 30.83/4.25  % (13013)------------------------------
% 30.83/4.25  % (13013)------------------------------
% 30.83/4.26  % (13017)Termination reason: Time limit
% 30.83/4.26  % (13017)Termination phase: Saturation
% 30.83/4.26  
% 30.83/4.26  % (13017)Memory used [KB]: 14328
% 30.83/4.26  % (13017)Time elapsed: 3.300 s
% 30.83/4.27  % (13017)------------------------------
% 30.83/4.27  % (13017)------------------------------
% 39.19/5.34  % (12976)Time limit reached!
% 39.19/5.34  % (12976)------------------------------
% 39.19/5.34  % (12976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 39.19/5.34  % (12976)Termination reason: Time limit
% 39.19/5.34  
% 39.19/5.34  % (12976)Memory used [KB]: 41449
% 39.19/5.34  % (12976)Time elapsed: 4.857 s
% 39.19/5.34  % (12976)------------------------------
% 39.19/5.34  % (12976)------------------------------
% 55.36/7.32  % (13020)Refutation found. Thanks to Tanya!
% 55.36/7.32  % SZS status Theorem for theBenchmark
% 55.36/7.32  % SZS output start Proof for theBenchmark
% 55.36/7.32  fof(f38621,plain,(
% 55.36/7.32    $false),
% 55.36/7.32    inference(avatar_sat_refutation,[],[f411,f1010,f38233,f38451])).
% 55.36/7.32  fof(f38451,plain,(
% 55.36/7.32    ~spl6_28),
% 55.36/7.32    inference(avatar_contradiction_clause,[],[f38450])).
% 55.36/7.32  fof(f38450,plain,(
% 55.36/7.32    $false | ~spl6_28),
% 55.36/7.32    inference(subsumption_resolution,[],[f38239,f144])).
% 55.36/7.32  fof(f144,plain,(
% 55.36/7.32    r2_relset_1(sK0,sK0,sK2,sK2)),
% 55.36/7.32    inference(resolution,[],[f118,f56])).
% 55.36/7.32  fof(f56,plain,(
% 55.36/7.32    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f29,plain,(
% 55.36/7.32    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 55.36/7.32    inference(flattening,[],[f28])).
% 55.36/7.32  fof(f28,plain,(
% 55.36/7.32    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 55.36/7.32    inference(ennf_transformation,[],[f25])).
% 55.36/7.32  fof(f25,negated_conjecture,(
% 55.36/7.32    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 55.36/7.32    inference(negated_conjecture,[],[f24])).
% 55.36/7.32  fof(f24,conjecture,(
% 55.36/7.32    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).
% 55.36/7.32  fof(f118,plain,(
% 55.36/7.32    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 55.36/7.32    inference(duplicate_literal_removal,[],[f117])).
% 55.36/7.32  fof(f117,plain,(
% 55.36/7.32    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 55.36/7.32    inference(equality_resolution,[],[f100])).
% 55.36/7.32  fof(f100,plain,(
% 55.36/7.32    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f45])).
% 55.36/7.32  fof(f45,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.36/7.32    inference(flattening,[],[f44])).
% 55.36/7.32  fof(f44,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 55.36/7.32    inference(ennf_transformation,[],[f14])).
% 55.36/7.32  fof(f14,axiom,(
% 55.36/7.32    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 55.36/7.32  fof(f38239,plain,(
% 55.36/7.32    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl6_28),
% 55.36/7.32    inference(backward_demodulation,[],[f59,f1009])).
% 55.36/7.32  fof(f1009,plain,(
% 55.36/7.32    sK2 = k6_partfun1(sK0) | ~spl6_28),
% 55.36/7.32    inference(avatar_component_clause,[],[f1007])).
% 55.36/7.32  fof(f1007,plain,(
% 55.36/7.32    spl6_28 <=> sK2 = k6_partfun1(sK0)),
% 55.36/7.32    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 55.36/7.32  fof(f59,plain,(
% 55.36/7.32    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f38233,plain,(
% 55.36/7.32    spl6_3 | spl6_27),
% 55.36/7.32    inference(avatar_contradiction_clause,[],[f38232])).
% 55.36/7.32  fof(f38232,plain,(
% 55.36/7.32    $false | (spl6_3 | spl6_27)),
% 55.36/7.32    inference(subsumption_resolution,[],[f38231,f8819])).
% 55.36/7.32  fof(f8819,plain,(
% 55.36/7.32    v1_funct_1(k6_partfun1(sK0))),
% 55.36/7.32    inference(forward_demodulation,[],[f8818,f201])).
% 55.36/7.32  fof(f201,plain,(
% 55.36/7.32    sK0 = k1_relat_1(sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f199,f62])).
% 55.36/7.32  fof(f62,plain,(
% 55.36/7.32    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f199,plain,(
% 55.36/7.32    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 55.36/7.32    inference(superposition,[],[f172,f84])).
% 55.36/7.32  fof(f84,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f37])).
% 55.36/7.32  fof(f37,plain,(
% 55.36/7.32    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.36/7.32    inference(ennf_transformation,[],[f11])).
% 55.36/7.32  fof(f11,axiom,(
% 55.36/7.32    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 55.36/7.32  fof(f172,plain,(
% 55.36/7.32    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f171,f60])).
% 55.36/7.32  fof(f60,plain,(
% 55.36/7.32    v1_funct_1(sK1)),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f171,plain,(
% 55.36/7.32    ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f163,f61])).
% 55.36/7.32  fof(f61,plain,(
% 55.36/7.32    v1_funct_2(sK1,sK0,sK0)),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f163,plain,(
% 55.36/7.32    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 55.36/7.32    inference(resolution,[],[f74,f62])).
% 55.36/7.32  fof(f74,plain,(
% 55.36/7.32    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 55.36/7.32    inference(cnf_transformation,[],[f35])).
% 55.36/7.32  fof(f35,plain,(
% 55.36/7.32    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 55.36/7.32    inference(flattening,[],[f34])).
% 55.36/7.32  fof(f34,plain,(
% 55.36/7.32    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 55.36/7.32    inference(ennf_transformation,[],[f23])).
% 55.36/7.32  fof(f23,axiom,(
% 55.36/7.32    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 55.36/7.32  fof(f8818,plain,(
% 55.36/7.32    v1_funct_1(k6_partfun1(k1_relat_1(sK1)))),
% 55.36/7.32    inference(subsumption_resolution,[],[f8817,f128])).
% 55.36/7.32  fof(f128,plain,(
% 55.36/7.32    v1_relat_1(sK1)),
% 55.36/7.32    inference(resolution,[],[f83,f62])).
% 55.36/7.32  fof(f83,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f36])).
% 55.36/7.32  fof(f36,plain,(
% 55.36/7.32    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.36/7.32    inference(ennf_transformation,[],[f9])).
% 55.36/7.32  fof(f9,axiom,(
% 55.36/7.32    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 55.36/7.32  fof(f8817,plain,(
% 55.36/7.32    v1_funct_1(k6_partfun1(k1_relat_1(sK1))) | ~v1_relat_1(sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f8816,f58])).
% 55.36/7.32  fof(f58,plain,(
% 55.36/7.32    v2_funct_1(sK1)),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f8816,plain,(
% 55.36/7.32    v1_funct_1(k6_partfun1(k1_relat_1(sK1))) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f8815,f60])).
% 55.36/7.32  fof(f8815,plain,(
% 55.36/7.32    v1_funct_1(k6_partfun1(k1_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 55.36/7.32    inference(superposition,[],[f8579,f112])).
% 55.36/7.32  fof(f112,plain,(
% 55.36/7.32    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.36/7.32    inference(definition_unfolding,[],[f72,f64])).
% 55.36/7.32  fof(f64,plain,(
% 55.36/7.32    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f18])).
% 55.36/7.32  fof(f18,axiom,(
% 55.36/7.32    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 55.36/7.32  fof(f72,plain,(
% 55.36/7.32    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f33])).
% 55.36/7.32  fof(f33,plain,(
% 55.36/7.32    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.36/7.32    inference(flattening,[],[f32])).
% 55.36/7.32  fof(f32,plain,(
% 55.36/7.32    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.36/7.32    inference(ennf_transformation,[],[f8])).
% 55.36/7.32  fof(f8,axiom,(
% 55.36/7.32    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 55.36/7.32  fof(f8579,plain,(
% 55.36/7.32    v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)))),
% 55.36/7.32    inference(subsumption_resolution,[],[f8556,f1875])).
% 55.36/7.32  fof(f1875,plain,(
% 55.36/7.32    v1_funct_1(k2_funct_1(sK1))),
% 55.36/7.32    inference(subsumption_resolution,[],[f1874,f60])).
% 55.36/7.32  fof(f1874,plain,(
% 55.36/7.32    ~v1_funct_1(sK1) | v1_funct_1(k2_funct_1(sK1))),
% 55.36/7.32    inference(subsumption_resolution,[],[f1873,f58])).
% 55.36/7.32  fof(f1873,plain,(
% 55.36/7.32    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | v1_funct_1(k2_funct_1(sK1))),
% 55.36/7.32    inference(subsumption_resolution,[],[f1860,f218])).
% 55.36/7.32  fof(f218,plain,(
% 55.36/7.32    v1_funct_2(sK1,sK0,k2_relat_1(sK1))),
% 55.36/7.32    inference(subsumption_resolution,[],[f217,f128])).
% 55.36/7.32  fof(f217,plain,(
% 55.36/7.32    v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f214,f60])).
% 55.36/7.32  fof(f214,plain,(
% 55.36/7.32    v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 55.36/7.32    inference(superposition,[],[f70,f201])).
% 55.36/7.32  fof(f70,plain,(
% 55.36/7.32    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f31])).
% 55.36/7.32  fof(f31,plain,(
% 55.36/7.32    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.36/7.32    inference(flattening,[],[f30])).
% 55.36/7.32  fof(f30,plain,(
% 55.36/7.32    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.36/7.32    inference(ennf_transformation,[],[f22])).
% 55.36/7.32  fof(f22,axiom,(
% 55.36/7.32    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 55.36/7.32  fof(f1860,plain,(
% 55.36/7.32    ~v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | v1_funct_1(k2_funct_1(sK1))),
% 55.36/7.32    inference(resolution,[],[f791,f216])).
% 55.36/7.32  fof(f216,plain,(
% 55.36/7.32    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 55.36/7.32    inference(subsumption_resolution,[],[f215,f128])).
% 55.36/7.32  fof(f215,plain,(
% 55.36/7.32    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~v1_relat_1(sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f213,f60])).
% 55.36/7.32  fof(f213,plain,(
% 55.36/7.32    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 55.36/7.32    inference(superposition,[],[f71,f201])).
% 55.36/7.32  fof(f71,plain,(
% 55.36/7.32    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f31])).
% 55.36/7.32  fof(f791,plain,(
% 55.36/7.32    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) | ~v1_funct_2(X0,X1,k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 55.36/7.32    inference(equality_resolution,[],[f192])).
% 55.36/7.32  fof(f192,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))) )),
% 55.36/7.32    inference(duplicate_literal_removal,[],[f191])).
% 55.36/7.32  fof(f191,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.36/7.32    inference(superposition,[],[f88,f85])).
% 55.36/7.32  fof(f85,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f38])).
% 55.36/7.32  fof(f38,plain,(
% 55.36/7.32    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.36/7.32    inference(ennf_transformation,[],[f12])).
% 55.36/7.32  fof(f12,axiom,(
% 55.36/7.32    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 55.36/7.32  fof(f88,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f41])).
% 55.36/7.32  fof(f41,plain,(
% 55.36/7.32    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 55.36/7.32    inference(flattening,[],[f40])).
% 55.36/7.32  fof(f40,plain,(
% 55.36/7.32    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 55.36/7.32    inference(ennf_transformation,[],[f21])).
% 55.36/7.32  fof(f21,axiom,(
% 55.36/7.32    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 55.36/7.32  fof(f8556,plain,(
% 55.36/7.32    v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1))),
% 55.36/7.32    inference(resolution,[],[f8537,f1854])).
% 55.36/7.32  fof(f1854,plain,(
% 55.36/7.32    ( ! [X39,X38,X40] : (~r1_tarski(X38,k2_zfmisc_1(X39,X40)) | v1_funct_1(k5_relat_1(sK1,X38)) | ~v1_funct_1(X38)) )),
% 55.36/7.32    inference(subsumption_resolution,[],[f1842,f60])).
% 55.36/7.32  fof(f1842,plain,(
% 55.36/7.32    ( ! [X39,X38,X40] : (~v1_funct_1(X38) | v1_funct_1(k5_relat_1(sK1,X38)) | ~v1_funct_1(sK1) | ~r1_tarski(X38,k2_zfmisc_1(X39,X40))) )),
% 55.36/7.32    inference(resolution,[],[f778,f62])).
% 55.36/7.32  fof(f778,plain,(
% 55.36/7.32    ( ! [X66,X64,X62,X67,X65,X63] : (~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) | ~v1_funct_1(X65) | v1_funct_1(k5_relat_1(X62,X65)) | ~v1_funct_1(X62) | ~r1_tarski(X65,k2_zfmisc_1(X66,X67))) )),
% 55.36/7.32    inference(resolution,[],[f270,f78])).
% 55.36/7.32  fof(f78,plain,(
% 55.36/7.32    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f4])).
% 55.36/7.32  fof(f4,axiom,(
% 55.36/7.32    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 55.36/7.32  fof(f270,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | v1_funct_1(k5_relat_1(X4,X5)) | ~v1_funct_1(X4)) )),
% 55.36/7.32    inference(duplicate_literal_removal,[],[f269])).
% 55.36/7.32  fof(f269,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 55.36/7.32    inference(superposition,[],[f103,f102])).
% 55.36/7.32  fof(f102,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f47])).
% 55.36/7.32  fof(f47,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 55.36/7.32    inference(flattening,[],[f46])).
% 55.36/7.32  fof(f46,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 55.36/7.32    inference(ennf_transformation,[],[f17])).
% 55.36/7.32  fof(f17,axiom,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 55.36/7.32  fof(f103,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f49])).
% 55.36/7.32  fof(f49,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 55.36/7.32    inference(flattening,[],[f48])).
% 55.36/7.32  fof(f48,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 55.36/7.32    inference(ennf_transformation,[],[f15])).
% 55.36/7.32  fof(f15,axiom,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 55.36/7.32  fof(f8537,plain,(
% 55.36/7.32    r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0))),
% 55.36/7.32    inference(subsumption_resolution,[],[f8536,f218])).
% 55.36/7.32  fof(f8536,plain,(
% 55.36/7.32    ~v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0))),
% 55.36/7.32    inference(subsumption_resolution,[],[f8535,f60])).
% 55.36/7.32  fof(f8535,plain,(
% 55.36/7.32    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0))),
% 55.36/7.32    inference(subsumption_resolution,[],[f8516,f58])).
% 55.36/7.32  fof(f8516,plain,(
% 55.36/7.32    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | r1_tarski(k2_funct_1(sK1),k2_zfmisc_1(k2_relat_1(sK1),sK0))),
% 55.36/7.32    inference(resolution,[],[f2133,f216])).
% 55.36/7.32  fof(f2133,plain,(
% 55.36/7.32    ( ! [X64,X63] : (~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X64,k2_relat_1(X63)))) | ~v2_funct_1(X63) | ~v1_funct_1(X63) | ~v1_funct_2(X63,X64,k2_relat_1(X63)) | r1_tarski(k2_funct_1(X63),k2_zfmisc_1(k2_relat_1(X63),X64))) )),
% 55.36/7.32    inference(resolution,[],[f907,f79])).
% 55.36/7.32  fof(f79,plain,(
% 55.36/7.32    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f4])).
% 55.36/7.32  fof(f907,plain,(
% 55.36/7.32    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,k2_relat_1(X0))) )),
% 55.36/7.32    inference(equality_resolution,[],[f258])).
% 55.36/7.32  fof(f258,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 55.36/7.32    inference(duplicate_literal_removal,[],[f257])).
% 55.36/7.32  fof(f257,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.36/7.32    inference(superposition,[],[f90,f85])).
% 55.36/7.32  fof(f90,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f41])).
% 55.36/7.32  fof(f38231,plain,(
% 55.36/7.32    ~v1_funct_1(k6_partfun1(sK0)) | (spl6_3 | spl6_27)),
% 55.36/7.32    inference(resolution,[],[f38230,f139])).
% 55.36/7.32  fof(f139,plain,(
% 55.36/7.32    ( ! [X0] : (v1_funct_2(k6_partfun1(X0),X0,X0) | ~v1_funct_1(k6_partfun1(X0))) )),
% 55.36/7.32    inference(forward_demodulation,[],[f138,f109])).
% 55.36/7.32  fof(f109,plain,(
% 55.36/7.32    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 55.36/7.32    inference(definition_unfolding,[],[f69,f64])).
% 55.36/7.32  fof(f69,plain,(
% 55.36/7.32    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 55.36/7.32    inference(cnf_transformation,[],[f6])).
% 55.36/7.32  fof(f6,axiom,(
% 55.36/7.32    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 55.36/7.32  fof(f138,plain,(
% 55.36/7.32    ( ! [X0] : (v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0))) | ~v1_funct_1(k6_partfun1(X0))) )),
% 55.36/7.32    inference(subsumption_resolution,[],[f136,f108])).
% 55.36/7.32  fof(f108,plain,(
% 55.36/7.32    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 55.36/7.32    inference(definition_unfolding,[],[f65,f64])).
% 55.36/7.32  fof(f65,plain,(
% 55.36/7.32    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f7])).
% 55.36/7.32  fof(f7,axiom,(
% 55.36/7.32    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 55.36/7.32  fof(f136,plain,(
% 55.36/7.32    ( ! [X0] : (v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0))) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 55.36/7.32    inference(superposition,[],[f70,f110])).
% 55.36/7.32  fof(f110,plain,(
% 55.36/7.32    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 55.36/7.32    inference(definition_unfolding,[],[f68,f64])).
% 55.36/7.32  fof(f68,plain,(
% 55.36/7.32    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 55.36/7.32    inference(cnf_transformation,[],[f6])).
% 55.36/7.32  fof(f38230,plain,(
% 55.36/7.32    ~v1_funct_2(k6_partfun1(sK0),sK0,sK0) | (spl6_3 | spl6_27)),
% 55.36/7.32    inference(subsumption_resolution,[],[f38229,f62])).
% 55.36/7.32  fof(f38229,plain,(
% 55.36/7.32    ~v1_funct_2(k6_partfun1(sK0),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl6_3 | spl6_27)),
% 55.36/7.32    inference(subsumption_resolution,[],[f38228,f1005])).
% 55.36/7.32  fof(f1005,plain,(
% 55.36/7.32    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2) | spl6_27),
% 55.36/7.32    inference(avatar_component_clause,[],[f1003])).
% 55.36/7.32  fof(f1003,plain,(
% 55.36/7.32    spl6_27 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2)),
% 55.36/7.32    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 55.36/7.32  fof(f38228,plain,(
% 55.36/7.32    ~v1_funct_2(k6_partfun1(sK0),sK0,sK0) | r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f38227,f67])).
% 55.36/7.32  fof(f67,plain,(
% 55.36/7.32    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f26])).
% 55.36/7.32  fof(f26,plain,(
% 55.36/7.32    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 55.36/7.32    inference(pure_predicate_removal,[],[f16])).
% 55.36/7.32  fof(f16,axiom,(
% 55.36/7.32    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 55.36/7.32  fof(f38227,plain,(
% 55.36/7.32    ~v1_funct_2(k6_partfun1(sK0),sK0,sK0) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f38217,f8819])).
% 55.36/7.32  fof(f38217,plain,(
% 55.36/7.32    ~v1_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(k6_partfun1(sK0),sK0,sK0) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_3),
% 55.36/7.32    inference(resolution,[],[f2066,f197])).
% 55.36/7.32  fof(f197,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.36/7.32    inference(subsumption_resolution,[],[f196,f67])).
% 55.36/7.32  fof(f196,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 55.36/7.32    inference(duplicate_literal_removal,[],[f193])).
% 55.36/7.32  fof(f193,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 55.36/7.32    inference(superposition,[],[f86,f105])).
% 55.36/7.32  fof(f105,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f51])).
% 55.36/7.32  fof(f51,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.36/7.32    inference(flattening,[],[f50])).
% 55.36/7.32  fof(f50,plain,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 55.36/7.32    inference(ennf_transformation,[],[f13])).
% 55.36/7.32  fof(f13,axiom,(
% 55.36/7.32    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 55.36/7.32  fof(f86,plain,(
% 55.36/7.32    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f39])).
% 55.36/7.32  fof(f39,plain,(
% 55.36/7.32    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.36/7.32    inference(ennf_transformation,[],[f19])).
% 55.36/7.32  fof(f19,axiom,(
% 55.36/7.32    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 55.36/7.32  fof(f2066,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,X1,sK2)) ) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f2065,f58])).
% 55.36/7.32  fof(f2065,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) ) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f2064,f60])).
% 55.36/7.32  fof(f2064,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) ) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f2063,f56])).
% 55.36/7.32  fof(f2063,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) ) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f2062,f55])).
% 55.36/7.32  fof(f55,plain,(
% 55.36/7.32    v1_funct_2(sK2,sK0,sK0)),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f2062,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) ) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f2061,f54])).
% 55.36/7.32  fof(f54,plain,(
% 55.36/7.32    v1_funct_1(sK2)),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f2061,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) ) | spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f2060,f359])).
% 55.36/7.32  fof(f359,plain,(
% 55.36/7.32    k1_xboole_0 != sK0 | spl6_3),
% 55.36/7.32    inference(avatar_component_clause,[],[f358])).
% 55.36/7.32  fof(f358,plain,(
% 55.36/7.32    spl6_3 <=> k1_xboole_0 = sK0),
% 55.36/7.32    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 55.36/7.32  fof(f2060,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | k1_xboole_0 = sK0 | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) )),
% 55.36/7.32    inference(subsumption_resolution,[],[f2059,f62])).
% 55.36/7.32  fof(f2059,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) )),
% 55.36/7.32    inference(subsumption_resolution,[],[f2056,f61])).
% 55.36/7.32  fof(f2056,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) )),
% 55.36/7.32    inference(duplicate_literal_removal,[],[f2049])).
% 55.36/7.32  fof(f2049,plain,(
% 55.36/7.32    ( ! [X1] : (~r2_relset_1(sK0,sK0,k5_relat_1(X1,sK1),sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | r2_relset_1(sK0,sK0,X1,sK2) | ~v2_funct_1(sK1)) )),
% 55.36/7.32    inference(superposition,[],[f347,f1968])).
% 55.36/7.32  fof(f1968,plain,(
% 55.36/7.32    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 55.36/7.32    inference(subsumption_resolution,[],[f1967,f54])).
% 55.36/7.32  fof(f1967,plain,(
% 55.36/7.32    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~v1_funct_1(sK2)),
% 55.36/7.32    inference(subsumption_resolution,[],[f1966,f62])).
% 55.36/7.32  fof(f1966,plain,(
% 55.36/7.32    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 55.36/7.32    inference(subsumption_resolution,[],[f1965,f60])).
% 55.36/7.32  fof(f1965,plain,(
% 55.36/7.32    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 55.36/7.32    inference(subsumption_resolution,[],[f1962,f56])).
% 55.36/7.32  fof(f1962,plain,(
% 55.36/7.32    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 55.36/7.32    inference(resolution,[],[f529,f57])).
% 55.36/7.32  fof(f57,plain,(
% 55.36/7.32    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 55.36/7.32    inference(cnf_transformation,[],[f29])).
% 55.36/7.32  fof(f529,plain,(
% 55.36/7.32    ( ! [X6,X4,X7,X5] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,X4,X5,sK0,X6,X7),sK1) | sK1 = k1_partfun1(sK0,X4,X5,sK0,X6,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK0))) | ~v1_funct_1(X6)) )),
% 55.36/7.32    inference(resolution,[],[f184,f104])).
% 55.36/7.32  fof(f104,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f49])).
% 55.36/7.32  fof(f184,plain,(
% 55.36/7.32    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X1 | ~r2_relset_1(sK0,sK0,X1,sK1)) )),
% 55.36/7.32    inference(resolution,[],[f101,f62])).
% 55.36/7.32  fof(f101,plain,(
% 55.36/7.32    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f45])).
% 55.36/7.32  fof(f347,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4)) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | r2_relset_1(X0,X1,X3,X5) | ~v2_funct_1(X4)) )),
% 55.36/7.32    inference(duplicate_literal_removal,[],[f344])).
% 55.36/7.32  fof(f344,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4)) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | r2_relset_1(X0,X1,X3,X5) | ~v2_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) )),
% 55.36/7.32    inference(superposition,[],[f96,f102])).
% 55.36/7.32  fof(f96,plain,(
% 55.36/7.32    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~v1_funct_1(X4) | ~v1_funct_2(X4,X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_1(X2) | r2_relset_1(X3,X0,X4,X5) | ~v2_funct_1(X2)) )),
% 55.36/7.32    inference(cnf_transformation,[],[f43])).
% 55.36/7.32  fof(f43,plain,(
% 55.36/7.32    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 55.36/7.32    inference(flattening,[],[f42])).
% 55.36/7.32  fof(f42,plain,(
% 55.36/7.32    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 55.36/7.32    inference(ennf_transformation,[],[f20])).
% 55.36/7.32  fof(f20,axiom,(
% 55.36/7.32    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).
% 55.36/7.32  fof(f1010,plain,(
% 55.36/7.32    ~spl6_27 | spl6_28),
% 55.36/7.32    inference(avatar_split_clause,[],[f514,f1007,f1003])).
% 55.36/7.32  fof(f514,plain,(
% 55.36/7.32    sK2 = k6_partfun1(sK0) | ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),sK2)),
% 55.36/7.32    inference(resolution,[],[f183,f67])).
% 55.36/7.32  fof(f183,plain,(
% 55.36/7.32    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = X0 | ~r2_relset_1(sK0,sK0,X0,sK2)) )),
% 55.36/7.32    inference(resolution,[],[f101,f56])).
% 55.36/7.32  fof(f411,plain,(
% 55.36/7.32    ~spl6_3),
% 55.36/7.32    inference(avatar_contradiction_clause,[],[f410])).
% 55.36/7.32  fof(f410,plain,(
% 55.36/7.32    $false | ~spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f408,f147])).
% 55.36/7.32  fof(f147,plain,(
% 55.36/7.32    ( ! [X2,X1] : (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)) )),
% 55.36/7.32    inference(resolution,[],[f118,f63])).
% 55.36/7.32  fof(f63,plain,(
% 55.36/7.32    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 55.36/7.32    inference(cnf_transformation,[],[f3])).
% 55.36/7.32  fof(f3,axiom,(
% 55.36/7.32    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 55.36/7.32  fof(f408,plain,(
% 55.36/7.32    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_3),
% 55.36/7.32    inference(backward_demodulation,[],[f395,f402])).
% 55.36/7.32  fof(f402,plain,(
% 55.36/7.32    k1_xboole_0 = sK2 | ~spl6_3),
% 55.36/7.32    inference(forward_demodulation,[],[f401,f115])).
% 55.36/7.32  fof(f115,plain,(
% 55.36/7.32    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 55.36/7.32    inference(equality_resolution,[],[f82])).
% 55.36/7.32  fof(f82,plain,(
% 55.36/7.32    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 55.36/7.32    inference(cnf_transformation,[],[f2])).
% 55.36/7.32  fof(f2,axiom,(
% 55.36/7.32    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 55.36/7.32  fof(f401,plain,(
% 55.36/7.32    sK2 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~spl6_3),
% 55.36/7.32    inference(forward_demodulation,[],[f400,f360])).
% 55.36/7.32  fof(f360,plain,(
% 55.36/7.32    k1_xboole_0 = sK0 | ~spl6_3),
% 55.36/7.32    inference(avatar_component_clause,[],[f358])).
% 55.36/7.32  fof(f400,plain,(
% 55.36/7.32    sK2 = k2_zfmisc_1(sK0,sK0) | ~spl6_3),
% 55.36/7.32    inference(subsumption_resolution,[],[f399,f121])).
% 55.36/7.32  fof(f121,plain,(
% 55.36/7.32    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 55.36/7.32    inference(resolution,[],[f79,f63])).
% 55.36/7.32  fof(f399,plain,(
% 55.36/7.32    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK0) | ~spl6_3),
% 55.36/7.32    inference(forward_demodulation,[],[f375,f115])).
% 55.36/7.32  fof(f375,plain,(
% 55.36/7.32    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK0) | ~spl6_3),
% 55.36/7.32    inference(backward_demodulation,[],[f135,f360])).
% 55.36/7.32  fof(f135,plain,(
% 55.36/7.32    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK2) | sK2 = k2_zfmisc_1(sK0,sK0)),
% 55.36/7.32    inference(resolution,[],[f77,f123])).
% 55.36/7.32  fof(f123,plain,(
% 55.36/7.32    r1_tarski(sK2,k2_zfmisc_1(sK0,sK0))),
% 55.36/7.32    inference(resolution,[],[f79,f56])).
% 55.36/7.32  fof(f77,plain,(
% 55.36/7.32    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 55.36/7.32    inference(cnf_transformation,[],[f1])).
% 55.36/7.32  fof(f1,axiom,(
% 55.36/7.32    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 55.36/7.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 55.36/7.32  fof(f395,plain,(
% 55.36/7.32    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | ~spl6_3),
% 55.36/7.32    inference(forward_demodulation,[],[f370,f254])).
% 55.36/7.32  fof(f254,plain,(
% 55.36/7.32    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 55.36/7.32    inference(subsumption_resolution,[],[f253,f121])).
% 55.36/7.32  fof(f253,plain,(
% 55.36/7.32    ~r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) | k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 55.36/7.32    inference(resolution,[],[f126,f77])).
% 55.36/7.32  fof(f126,plain,(
% 55.36/7.32    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)),
% 55.36/7.32    inference(resolution,[],[f79,f119])).
% 55.36/7.32  fof(f119,plain,(
% 55.36/7.32    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 55.36/7.32    inference(superposition,[],[f67,f115])).
% 55.36/7.32  fof(f370,plain,(
% 55.36/7.32    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k6_partfun1(k1_xboole_0)) | ~spl6_3),
% 55.36/7.32    inference(backward_demodulation,[],[f59,f360])).
% 55.36/7.32  % SZS output end Proof for theBenchmark
% 55.36/7.32  % (13020)------------------------------
% 55.36/7.32  % (13020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 55.36/7.32  % (13020)Termination reason: Refutation
% 55.36/7.32  
% 55.36/7.32  % (13020)Memory used [KB]: 27121
% 55.36/7.32  % (13020)Time elapsed: 6.186 s
% 55.36/7.32  % (13020)------------------------------
% 55.36/7.32  % (13020)------------------------------
% 55.36/7.34  % (12955)Success in time 6.961 s
%------------------------------------------------------------------------------
