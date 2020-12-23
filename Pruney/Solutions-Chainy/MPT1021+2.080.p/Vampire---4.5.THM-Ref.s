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
% DateTime   : Thu Dec  3 13:06:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  135 (1144 expanded)
%              Number of leaves         :   15 ( 278 expanded)
%              Depth                    :   26
%              Number of atoms          :  402 (6097 expanded)
%              Number of equality atoms :   63 ( 177 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(subsumption_resolution,[],[f258,f78])).

fof(f78,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(resolution,[],[f67,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f258,plain,(
    ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f249,f257])).

fof(f257,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f255,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f37])).

fof(f37,plain,
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

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) ) ),
    inference(forward_demodulation,[],[f252,f101])).

fof(f101,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f87,f99])).

fof(f99,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f98,f71])).

fof(f71,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f70,f43])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f98,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f97,f75])).

fof(f75,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f97,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f96,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f96,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f95,f42])).

fof(f42,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0) ),
    inference(resolution,[],[f94,f43])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_2(sK1,X1)
      | ~ v3_funct_2(sK1,X0,X1) ) ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f87,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f86,f71])).

fof(f86,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f82,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f81,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f80,plain,
    ( v2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0) ),
    inference(resolution,[],[f79,f43])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_1(sK1)
      | ~ v3_funct_2(sK1,X0,X1) ) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) ) ),
    inference(resolution,[],[f251,f40])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0) ) ),
    inference(resolution,[],[f214,f151])).

fof(f151,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f150,f112])).

fof(f112,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f111,f40])).

fof(f111,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f110,f42])).

fof(f110,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f150,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f149,f41])).

fof(f149,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f148,f42])).

fof(f148,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f146,f43])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(sK1,X0,X0)
      | ~ v1_funct_2(sK1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

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

fof(f214,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_partfun1(X8,X9,X6,X7,k2_funct_1(sK1),X5) = k5_relat_1(k2_funct_1(sK1),X5) ) ),
    inference(resolution,[],[f65,f114])).

fof(f114,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f105,f112])).

fof(f105,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f41])).

fof(f104,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f103,f42])).

fof(f103,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f102,f43])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(sK1,X0,X0)
      | ~ v1_funct_2(sK1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,sK1)) ) ),
    inference(resolution,[],[f56,f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f249,plain,(
    ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f248,f78])).

fof(f248,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f118,f247])).

fof(f247,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f245,f151])).

fof(f245,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X2,X3,sK1,k2_funct_1(sK1)) ) ),
    inference(forward_demodulation,[],[f243,f191])).

fof(f191,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f89,f188])).

fof(f188,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f91,f187])).

fof(f187,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f186,f161])).

fof(f161,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f151,f70])).

fof(f186,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f185,f160])).

fof(f160,plain,(
    v5_relat_1(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f151,f60])).

fof(f185,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f162,f53])).

fof(f162,plain,(
    v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f156,f141])).

fof(f141,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f140,f112])).

fof(f140,plain,(
    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f139,f40])).

fof(f139,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f138,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f156,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(resolution,[],[f151,f123])).

fof(f123,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_2(k2_funct_1(sK1),X2)
      | ~ v3_funct_2(k2_funct_1(sK1),X1,X2) ) ),
    inference(forward_demodulation,[],[f122,f112])).

fof(f122,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v3_funct_2(k2_funct_1(sK1),X1,X2)
      | v2_funct_2(k2_funct_2(sK0,sK1),X2) ) ),
    inference(forward_demodulation,[],[f116,f112])).

fof(f116,plain,(
    ! [X2,X1] :
      ( ~ v3_funct_2(k2_funct_1(sK1),X1,X2)
      | ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_2(k2_funct_2(sK0,sK1),X2) ) ),
    inference(backward_demodulation,[],[f107,f112])).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_2(k2_funct_2(sK0,sK1),X2)
      | ~ v3_funct_2(k2_funct_2(sK0,sK1),X1,X2) ) ),
    inference(resolution,[],[f105,f63])).

fof(f91,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f90,f71])).

fof(f90,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f84,f40])).

fof(f84,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f81,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f89,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f88,f71])).

fof(f88,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f81,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f243,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,X2,X3,sK1,k2_funct_1(sK1)) ) ),
    inference(resolution,[],[f241,f114])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0) ) ),
    inference(resolution,[],[f213,f43])).

fof(f213,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f65,f40])).

fof(f118,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f113,f112])).

fof(f113,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f69,f112])).

fof(f69,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f68,f45])).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f68,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f44,f45])).

fof(f44,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n018.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 10:09:11 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.19/0.47  % (14127)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.48  % (14135)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (14127)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (14123)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f259,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(subsumption_resolution,[],[f258,f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.19/0.51    inference(resolution,[],[f67,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.19/0.51    inference(condensation,[],[f64])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(flattening,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.19/0.51  fof(f258,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.19/0.51    inference(backward_demodulation,[],[f249,f257])).
% 0.19/0.51  fof(f257,plain,(
% 0.19/0.51    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 0.19/0.51    inference(resolution,[],[f255,f43])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.51    inference(flattening,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.19/0.51    inference(negated_conjecture,[],[f14])).
% 0.19/0.51  fof(f14,conjecture,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 0.19/0.51  fof(f255,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f252,f101])).
% 0.19/0.51  fof(f101,plain,(
% 0.19/0.51    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.19/0.51    inference(backward_demodulation,[],[f87,f99])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    sK0 = k2_relat_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f98,f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    v1_relat_1(sK1)),
% 0.19/0.51    inference(resolution,[],[f70,f43])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.19/0.51    inference(resolution,[],[f47,f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f97,f75])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    v5_relat_1(sK1,sK0)),
% 0.19/0.51    inference(resolution,[],[f60,f43])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.51  fof(f97,plain,(
% 0.19/0.51    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(resolution,[],[f96,f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(nnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    v2_funct_2(sK1,sK0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f95,f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    v3_funct_2(sK1,sK0,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f95,plain,(
% 0.19/0.51    v2_funct_2(sK1,sK0) | ~v3_funct_2(sK1,sK0,sK0)),
% 0.19/0.51    inference(resolution,[],[f94,f43])).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_2(sK1,X1) | ~v3_funct_2(sK1,X0,X1)) )),
% 0.19/0.51    inference(resolution,[],[f63,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    v1_funct_1(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(flattening,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f86,f71])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f82,f40])).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(resolution,[],[f81,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    v2_funct_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f80,f42])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    v2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0)),
% 0.19/0.51    inference(resolution,[],[f79,f43])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_1(sK1) | ~v3_funct_2(sK1,X0,X1)) )),
% 0.19/0.51    inference(resolution,[],[f62,f40])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f32])).
% 0.19/0.51  fof(f252,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) )),
% 0.19/0.51    inference(resolution,[],[f251,f40])).
% 0.19/0.51  fof(f251,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0)) )),
% 0.19/0.51    inference(resolution,[],[f214,f151])).
% 0.19/0.51  fof(f151,plain,(
% 0.19/0.51    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.51    inference(forward_demodulation,[],[f150,f112])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f111,f40])).
% 0.19/0.51  fof(f111,plain,(
% 0.19/0.51    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f110,f42])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f109,f43])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.19/0.51    inference(resolution,[],[f55,f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.19/0.51    inference(flattening,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.19/0.51  fof(f150,plain,(
% 0.19/0.51    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f149,f41])).
% 0.19/0.51  fof(f149,plain,(
% 0.19/0.51    ~v1_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f148,f42])).
% 0.19/0.51  fof(f148,plain,(
% 0.19/0.51    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.51    inference(resolution,[],[f146,f43])).
% 0.19/0.51  fof(f146,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK1,X0,X0) | ~v1_funct_2(sK1,X0,X0) | m1_subset_1(k2_funct_2(X0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.51    inference(resolution,[],[f59,f40])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.19/0.51    inference(flattening,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.19/0.51  fof(f214,plain,(
% 0.19/0.51    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_partfun1(X8,X9,X6,X7,k2_funct_1(sK1),X5) = k5_relat_1(k2_funct_1(sK1),X5)) )),
% 0.19/0.51    inference(resolution,[],[f65,f114])).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    v1_funct_1(k2_funct_1(sK1))),
% 0.19/0.51    inference(backward_demodulation,[],[f105,f112])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f104,f41])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    ~v1_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f103,f42])).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.19/0.51    inference(resolution,[],[f102,f43])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(sK1,X0,X0) | ~v1_funct_2(sK1,X0,X0) | v1_funct_1(k2_funct_2(X0,sK1))) )),
% 0.19/0.51    inference(resolution,[],[f56,f40])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.51    inference(flattening,[],[f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.19/0.51  fof(f249,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.19/0.51    inference(subsumption_resolution,[],[f248,f78])).
% 0.19/0.51  fof(f248,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.19/0.51    inference(backward_demodulation,[],[f118,f247])).
% 0.19/0.51  fof(f247,plain,(
% 0.19/0.51    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.19/0.51    inference(resolution,[],[f245,f151])).
% 0.19/0.51  fof(f245,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X2,X3,sK1,k2_funct_1(sK1))) )),
% 0.19/0.51    inference(forward_demodulation,[],[f243,f191])).
% 0.19/0.51  fof(f191,plain,(
% 0.19/0.51    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 0.19/0.51    inference(backward_demodulation,[],[f89,f188])).
% 0.19/0.51  fof(f188,plain,(
% 0.19/0.51    sK0 = k1_relat_1(sK1)),
% 0.19/0.51    inference(backward_demodulation,[],[f91,f187])).
% 0.19/0.51  fof(f187,plain,(
% 0.19/0.51    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f186,f161])).
% 0.19/0.51  fof(f161,plain,(
% 0.19/0.51    v1_relat_1(k2_funct_1(sK1))),
% 0.19/0.51    inference(resolution,[],[f151,f70])).
% 0.19/0.51  fof(f186,plain,(
% 0.19/0.51    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f185,f160])).
% 0.19/0.51  fof(f160,plain,(
% 0.19/0.51    v5_relat_1(k2_funct_1(sK1),sK0)),
% 0.19/0.51    inference(resolution,[],[f151,f60])).
% 0.19/0.51  fof(f185,plain,(
% 0.19/0.51    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v5_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.19/0.51    inference(resolution,[],[f162,f53])).
% 0.19/0.51  fof(f162,plain,(
% 0.19/0.51    v2_funct_2(k2_funct_1(sK1),sK0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f156,f141])).
% 0.19/0.51  fof(f141,plain,(
% 0.19/0.51    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.19/0.51    inference(forward_demodulation,[],[f140,f112])).
% 0.19/0.51  fof(f140,plain,(
% 0.19/0.51    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f139,f40])).
% 0.19/0.51  fof(f139,plain,(
% 0.19/0.51    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f138,f41])).
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f137,f43])).
% 0.19/0.51  fof(f137,plain,(
% 0.19/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.19/0.51    inference(resolution,[],[f58,f42])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f156,plain,(
% 0.19/0.51    v2_funct_2(k2_funct_1(sK1),sK0) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.19/0.51    inference(resolution,[],[f151,f123])).
% 0.19/0.51  fof(f123,plain,(
% 0.19/0.51    ( ! [X2,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_2(k2_funct_1(sK1),X2) | ~v3_funct_2(k2_funct_1(sK1),X1,X2)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f122,f112])).
% 0.19/0.51  fof(f122,plain,(
% 0.19/0.51    ( ! [X2,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v3_funct_2(k2_funct_1(sK1),X1,X2) | v2_funct_2(k2_funct_2(sK0,sK1),X2)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f116,f112])).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    ( ! [X2,X1] : (~v3_funct_2(k2_funct_1(sK1),X1,X2) | ~m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_2(k2_funct_2(sK0,sK1),X2)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f107,f112])).
% 0.19/0.51  fof(f107,plain,(
% 0.19/0.51    ( ! [X2,X1] : (~m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_2(k2_funct_2(sK0,sK1),X2) | ~v3_funct_2(k2_funct_2(sK0,sK1),X1,X2)) )),
% 0.19/0.51    inference(resolution,[],[f105,f63])).
% 0.19/0.51  fof(f91,plain,(
% 0.19/0.51    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f90,f71])).
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f84,f40])).
% 0.19/0.51  fof(f84,plain,(
% 0.19/0.51    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(resolution,[],[f81,f49])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f88,f71])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f83,f40])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.51    inference(resolution,[],[f81,f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f243,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,X2,X3,sK1,k2_funct_1(sK1))) )),
% 0.19/0.51    inference(resolution,[],[f241,f114])).
% 0.19/0.51  fof(f241,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0)) )),
% 0.19/0.51    inference(resolution,[],[f213,f43])).
% 0.19/0.51  fof(f213,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0)) )),
% 0.19/0.51    inference(resolution,[],[f65,f40])).
% 0.19/0.51  fof(f118,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.19/0.51    inference(forward_demodulation,[],[f113,f112])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.19/0.51    inference(backward_demodulation,[],[f69,f112])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.19/0.51    inference(forward_demodulation,[],[f68,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.19/0.51    inference(backward_demodulation,[],[f44,f45])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (14127)------------------------------
% 0.19/0.51  % (14127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (14127)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (14127)Memory used [KB]: 6396
% 0.19/0.51  % (14127)Time elapsed: 0.078 s
% 0.19/0.51  % (14127)------------------------------
% 0.19/0.51  % (14127)------------------------------
% 0.19/0.51  % (14119)Success in time 0.174 s
%------------------------------------------------------------------------------
