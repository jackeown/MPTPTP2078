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
% DateTime   : Thu Dec  3 13:08:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 254 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :  256 (1177 expanded)
%              Number of equality atoms :   77 ( 239 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f78])).

fof(f78,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f28,f77])).

fof(f77,plain,(
    sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f76,f63])).

fof(f63,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f62,f52])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f60,f25])).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(superposition,[],[f49,f59])).

fof(f59,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f54,f58])).

fof(f58,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f57,f27])).

fof(f57,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK1,X0,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,sK1) = X0 ) ),
    inference(resolution,[],[f36,f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f54,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f38,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f49,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f76,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_partfun1(sK0)
    | sK1 = k6_partfun1(sK0) ),
    inference(superposition,[],[f72,f66])).

fof(f66,plain,
    ( sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = X0 ) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f24,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | k3_funct_2(sK0,sK0,sK1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f64,f52])).

fof(f64,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f61,f25])).

fof(f61,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(superposition,[],[f50,f59])).

fof(f50,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK2(X0,X1),X0)
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK2(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(resolution,[],[f71,f65])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f70,f31])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f69,f27])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f68,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f67,f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,X0)
      | k3_funct_2(X0,X1,sK1,X2) = k1_funct_1(sK1,X2) ) ),
    inference(resolution,[],[f42,f25])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f28,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f96,f27])).

fof(f96,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f95,f26])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,sK1,sK1) ) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK1,X0,X1)
      | k1_funct_1(sK1,sK3(X0,sK1,sK1)) != k1_funct_1(sK1,sK3(X0,sK1,sK1))
      | r2_funct_2(X0,X1,sK1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK1,X0,X1)
      | ~ v1_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(sK1,sK3(X0,sK1,sK1)) != k1_funct_1(sK1,sK3(X0,sK1,sK1))
      | r2_funct_2(X0,X1,sK1,sK1) ) ),
    inference(resolution,[],[f92,f25])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_2(sK1,X1,X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_funct_1(X0,sK3(X1,X0,sK1)) != k1_funct_1(sK1,sK3(X1,X0,sK1))
      | r2_funct_2(X1,X2,X0,sK1) ) ),
    inference(resolution,[],[f41,f25])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (18360)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (18360)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (18358)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f97,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f28,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f76,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f62,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f37,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f60,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    v1_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(superposition,[],[f49,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f54,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f57,f27])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f56,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_2(sK1,X0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,sK1) = X0) )),
% 0.20/0.52    inference(resolution,[],[f36,f25])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f38,f27])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k6_partfun1(X0) = X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_partfun1(sK0) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(superposition,[],[f72,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(resolution,[],[f65,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = X0) )),
% 0.20/0.52    inference(resolution,[],[f24,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,sK0) | k3_funct_2(sK0,sK0,sK1,X2) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f64,f52])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    r2_hidden(sK2(sK0,sK1),sK0) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f61,f25])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    r2_hidden(sK2(sK0,sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(superposition,[],[f50,f59])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK2(X0,X1),X0) | k6_partfun1(X0) = X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f30])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK2(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 0.20/0.52    inference(resolution,[],[f71,f65])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f70,f31])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f69,f27])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f68,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~v1_xboole_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f67,f26])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK1,X2) = k1_funct_1(sK1,X2)) )),
% 0.20/0.52    inference(resolution,[],[f42,f25])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f96,f27])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.20/0.52    inference(resolution,[],[f95,f26])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,sK1,sK1)) )),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK1,X0,X1) | k1_funct_1(sK1,sK3(X0,sK1,sK1)) != k1_funct_1(sK1,sK3(X0,sK1,sK1)) | r2_funct_2(X0,X1,sK1,sK1)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK1,X0,X1) | ~v1_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(sK1,sK3(X0,sK1,sK1)) != k1_funct_1(sK1,sK3(X0,sK1,sK1)) | r2_funct_2(X0,X1,sK1,sK1)) )),
% 0.20/0.52    inference(resolution,[],[f92,f25])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_2(sK1,X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_funct_1(X0,sK3(X1,X0,sK1)) != k1_funct_1(sK1,sK3(X1,X0,sK1)) | r2_funct_2(X1,X2,X0,sK1)) )),
% 0.20/0.52    inference(resolution,[],[f41,f25])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3)) | r2_funct_2(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (18360)------------------------------
% 0.20/0.52  % (18360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18360)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (18360)Memory used [KB]: 6268
% 0.20/0.52  % (18360)Time elapsed: 0.095 s
% 0.20/0.52  % (18360)------------------------------
% 0.20/0.52  % (18360)------------------------------
% 0.20/0.52  % (18353)Success in time 0.159 s
%------------------------------------------------------------------------------
