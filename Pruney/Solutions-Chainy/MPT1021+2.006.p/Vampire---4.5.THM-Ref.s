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
% DateTime   : Thu Dec  3 13:05:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 (1292 expanded)
%              Number of leaves         :   16 ( 315 expanded)
%              Depth                    :   23
%              Number of atoms          :  389 (6977 expanded)
%              Number of equality atoms :   64 ( 200 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f102])).

fof(f102,plain,(
    ! [X2] : r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2)) ),
    inference(resolution,[],[f73,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f358,plain,(
    ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f344,f357])).

fof(f357,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f356,f141])).

fof(f141,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f123,f140])).

fof(f140,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f103,f139])).

fof(f139,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f138,f43])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f138,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f44,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f135,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f103,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f123,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f122,f77])).

fof(f77,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f74,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f51,f46])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f122,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f118,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f116,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f116,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f112,f45])).

fof(f45,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f66,f46])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f356,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f353,f43])).

fof(f353,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f315,f46])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f310,f168])).

fof(f168,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f157,f167])).

fof(f167,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f166,f43])).

fof(f166,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f165,f44])).

fof(f165,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f162,f45])).

fof(f162,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f157,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f156,f43])).

fof(f156,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f155,f44])).

fof(f155,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f152,f45])).

fof(f152,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f69,f195])).

fof(f195,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f194,f167])).

fof(f194,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f193,f43])).

fof(f193,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f192,f44])).

fof(f192,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f189,f45])).

fof(f189,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f61,f46])).

% (7099)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f344,plain,(
    ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f343,f102])).

fof(f343,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f170,f342])).

fof(f342,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(forward_demodulation,[],[f341,f246])).

fof(f246,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(forward_demodulation,[],[f245,f125])).

fof(f125,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f124,f77])).

fof(f124,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f116,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f245,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) ),
    inference(forward_demodulation,[],[f244,f234])).

fof(f234,plain,(
    sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f198,f233])).

fof(f233,plain,(
    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f232,f168])).

fof(f232,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f206,f177])).

fof(f177,plain,(
    v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f176,f167])).

fof(f176,plain,(
    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f175,f43])).

fof(f175,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f174,f44])).

fof(f174,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f171,f45])).

fof(f171,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f206,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f195,f62])).

fof(f198,plain,(
    k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f195,f64])).

fof(f244,plain,(
    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f243,f200])).

fof(f200,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f195,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f243,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f237,f168])).

fof(f237,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f211,f53])).

fof(f211,plain,(
    v2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f210,f168])).

fof(f210,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f197,f184])).

fof(f184,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f183,f167])).

fof(f183,plain,(
    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f182,f43])).

fof(f182,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f181,f44])).

fof(f181,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f178,f45])).

fof(f178,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f195,f66])).

fof(f341,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(subsumption_resolution,[],[f335,f168])).

fof(f335,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f316,f195])).

fof(f316,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_partfun1(X10,X11,sK0,sK0,X12,sK1) = k5_relat_1(X12,sK1)
      | ~ v1_funct_1(X12) ) ),
    inference(subsumption_resolution,[],[f313,f43])).

fof(f313,plain,(
    ! [X12,X10,X11] :
      ( k1_partfun1(X10,X11,sK0,sK0,X12,sK1) = k5_relat_1(X12,sK1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X12) ) ),
    inference(resolution,[],[f69,f46])).

fof(f170,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f169,f167])).

fof(f169,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f70,f167])).

fof(f70,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f47,f48,f48])).

fof(f47,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:30:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (7109)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.43  % (7109)Refutation not found, incomplete strategy% (7109)------------------------------
% 0.22/0.43  % (7109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (7109)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (7109)Memory used [KB]: 10874
% 0.22/0.43  % (7109)Time elapsed: 0.011 s
% 0.22/0.43  % (7109)------------------------------
% 0.22/0.43  % (7109)------------------------------
% 0.22/0.46  % (7103)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (7104)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (7110)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (7111)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (7098)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (7111)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f359,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f358,f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X2] : (r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2))) )),
% 0.22/0.48    inference(resolution,[],[f73,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f50,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.48    inference(condensation,[],[f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.48  fof(f358,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.22/0.48    inference(backward_demodulation,[],[f344,f357])).
% 0.22/0.48  fof(f357,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f356,f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f123,f140])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    sK0 = k1_relat_1(sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f103,f139])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f138,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.48    inference(negated_conjecture,[],[f16])).
% 0.22/0.48  fof(f16,conjecture,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f135,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f62,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f64,f46])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f122,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.22/0.48    inference(resolution,[],[f51,f46])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f43])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f116,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    v2_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f115,f43])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f112,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f66,f46])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.48  fof(f356,plain,(
% 0.22/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f353,f43])).
% 0.22/0.48  fof(f353,plain,(
% 0.22/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f315,f46])).
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) | ~v1_funct_1(X2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f310,f168])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f157,f167])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f166,f43])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f165,f44])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f162,f45])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f57,f46])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f156,f43])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f155,f44])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f152,f45])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f58,f46])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.48  fof(f310,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.48    inference(resolution,[],[f69,f195])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f194,f167])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f193,f43])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f192,f44])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f189,f45])).
% 0.22/0.48  fof(f189,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f61,f46])).
% 0.22/0.48  % (7099)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.48    inference(flattening,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.48  fof(f344,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f343,f102])).
% 0.22/0.48  fof(f343,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.48    inference(backward_demodulation,[],[f170,f342])).
% 0.22/0.48  fof(f342,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 0.22/0.48    inference(forward_demodulation,[],[f341,f246])).
% 0.22/0.48  fof(f246,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.22/0.48    inference(forward_demodulation,[],[f245,f125])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f124,f77])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f119,f43])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f116,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.48  fof(f245,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1)))),
% 0.22/0.48    inference(forward_demodulation,[],[f244,f234])).
% 0.22/0.48  fof(f234,plain,(
% 0.22/0.48    sK0 = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f198,f233])).
% 0.22/0.48  fof(f233,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f232,f168])).
% 0.22/0.48  fof(f232,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f206,f177])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.48    inference(forward_demodulation,[],[f176,f167])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f175,f43])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f174,f44])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f171,f45])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f59,f46])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f195,f62])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f195,f64])).
% 0.22/0.48  fof(f244,plain,(
% 0.22/0.48    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f243,f200])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f195,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.48  fof(f243,plain,(
% 0.22/0.48    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f237,f168])).
% 0.22/0.48  fof(f237,plain,(
% 0.22/0.48    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f211,f53])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f210,f168])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f197,f184])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.48    inference(forward_demodulation,[],[f183,f167])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f182,f43])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f181,f44])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f178,f45])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f60,f46])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f195,f66])).
% 0.22/0.48  fof(f341,plain,(
% 0.22/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f335,f168])).
% 0.22/0.48  fof(f335,plain,(
% 0.22/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f316,f195])).
% 0.22/0.48  fof(f316,plain,(
% 0.22/0.48    ( ! [X12,X10,X11] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | k1_partfun1(X10,X11,sK0,sK0,X12,sK1) = k5_relat_1(X12,sK1) | ~v1_funct_1(X12)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f313,f43])).
% 0.22/0.48  fof(f313,plain,(
% 0.22/0.48    ( ! [X12,X10,X11] : (k1_partfun1(X10,X11,sK0,sK0,X12,sK1) = k5_relat_1(X12,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X12)) )),
% 0.22/0.48    inference(resolution,[],[f69,f46])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.48    inference(forward_demodulation,[],[f169,f167])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.48    inference(backward_demodulation,[],[f70,f167])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.22/0.48    inference(definition_unfolding,[],[f47,f48,f48])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7111)------------------------------
% 0.22/0.48  % (7111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7111)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7111)Memory used [KB]: 2046
% 0.22/0.48  % (7111)Time elapsed: 0.043 s
% 0.22/0.48  % (7111)------------------------------
% 0.22/0.48  % (7111)------------------------------
% 0.22/0.48  % (7097)Success in time 0.123 s
%------------------------------------------------------------------------------
