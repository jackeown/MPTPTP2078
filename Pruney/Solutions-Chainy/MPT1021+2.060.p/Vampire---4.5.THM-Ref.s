%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:59 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  193 (1318 expanded)
%              Number of leaves         :   24 ( 323 expanded)
%              Depth                    :   27
%              Number of atoms          :  572 (6809 expanded)
%              Number of equality atoms :  104 ( 243 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f929,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f342,f347,f922,f926])).

fof(f926,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f924,f129])).

fof(f129,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(resolution,[],[f95,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f924,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl2_2 ),
    inference(forward_demodulation,[],[f923,f371])).

fof(f371,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(forward_demodulation,[],[f370,f172])).

fof(f172,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f155,f171])).

fof(f171,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f170,f107])).

fof(f107,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f105,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f47])).

fof(f47,plain,
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

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f170,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f169,f115])).

fof(f115,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f81,f56])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f169,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f168,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f168,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f167,f53])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f167,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f165,f55])).

fof(f55,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f165,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f155,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f154,f107])).

fof(f154,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f152,f53])).

fof(f152,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f151,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f151,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f150,f53])).

fof(f150,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f148,f55])).

fof(f148,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f83,f56])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f370,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(subsumption_resolution,[],[f366,f240])).

fof(f240,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f208,f238])).

fof(f238,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f237,f53])).

fof(f237,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f236,f54])).

fof(f54,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f236,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f234,f55])).

fof(f234,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f72,f56])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f208,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f207,f53])).

fof(f207,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f206,f54])).

fof(f206,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f204,f55])).

fof(f204,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f73,f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f366,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f354,f302])).

fof(f302,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f301,f53])).

fof(f301,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f300,f54])).

fof(f300,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f299,f55])).

fof(f299,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f281,f56])).

fof(f281,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f76,f238])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f354,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | k1_partfun1(X12,X13,sK0,sK0,X14,sK1) = k5_relat_1(X14,sK1)
      | ~ v1_funct_1(X14) ) ),
    inference(subsumption_resolution,[],[f351,f53])).

fof(f351,plain,(
    ! [X14,X12,X13] :
      ( k1_partfun1(X12,X13,sK0,sK0,X14,sK1) = k5_relat_1(X14,sK1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ v1_funct_1(X14) ) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f923,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_2 ),
    inference(forward_demodulation,[],[f103,f238])).

fof(f103,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f922,plain,
    ( spl2_1
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f921])).

fof(f921,plain,
    ( $false
    | spl2_1
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f920,f129])).

fof(f920,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl2_1
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f241,f900])).

fof(f900,plain,
    ( k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f899,f699])).

fof(f699,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f157,f694])).

fof(f694,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f693,f378])).

fof(f378,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f377,f245])).

fof(f245,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl2_12
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f377,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f376,f308])).

fof(f308,plain,(
    v5_relat_1(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f302,f81])).

fof(f376,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f325,f70])).

fof(f325,plain,(
    v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f324,f240])).

fof(f324,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f305,f267])).

fof(f267,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f266,f238])).

fof(f266,plain,(
    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f265,f53])).

fof(f265,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f264,f54])).

fof(f264,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f262,f55])).

fof(f262,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f75,f56])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f305,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f302,f84])).

fof(f693,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f690,f261])).

fof(f261,plain,(
    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f260,f189])).

fof(f189,plain,(
    sK0 = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f164,f171])).

fof(f164,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f163,f110])).

fof(f110,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(resolution,[],[f61,f107])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f163,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f162,f107])).

fof(f162,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f158,f53])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f68,f92])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f260,plain,(
    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f259,f107])).

fof(f259,plain,
    ( k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f258,f53])).

fof(f258,plain,
    ( k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f188,f151])).

fof(f188,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f65,f92])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f690,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl2_12 ),
    inference(superposition,[],[f355,f375])).

fof(f375,plain,
    ( k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f374,f245])).

fof(f374,plain,
    ( k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f309,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f309,plain,(
    v4_relat_1(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f302,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f355,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(k2_funct_1(sK1),X0)
    | ~ spl2_12 ),
    inference(resolution,[],[f245,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f157,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f156,f107])).

fof(f156,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f153,f53])).

fof(f153,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f151,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f899,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f894,f53])).

fof(f894,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f735,f56])).

fof(f735,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_1(sK1)) = k5_relat_1(X15,k2_funct_1(sK1))
      | ~ v1_funct_1(X15) ) ),
    inference(forward_demodulation,[],[f734,f238])).

fof(f734,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | ~ v1_funct_1(X15)
      | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f733,f53])).

fof(f733,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | ~ v1_funct_1(X15)
      | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1))
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f732,f54])).

fof(f732,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | ~ v1_funct_1(X15)
      | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f721,f55])).

fof(f721,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | ~ v1_funct_1(X15)
      | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1))
      | ~ v3_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f353,f56])).

fof(f353,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X9)))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X10)
      | k1_partfun1(X7,X8,X9,X9,X10,k2_funct_2(X9,X11)) = k5_relat_1(X10,k2_funct_2(X9,X11))
      | ~ v3_funct_2(X11,X9,X9)
      | ~ v1_funct_2(X11,X9,X9)
      | ~ v1_funct_1(X11) ) ),
    inference(subsumption_resolution,[],[f350,f73])).

fof(f350,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( k1_partfun1(X7,X8,X9,X9,X10,k2_funct_2(X9,X11)) = k5_relat_1(X10,k2_funct_2(X9,X11))
      | ~ v1_funct_1(k2_funct_2(X9,X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X9)))
      | ~ v3_funct_2(X11,X9,X9)
      | ~ v1_funct_2(X11,X9,X9)
      | ~ v1_funct_1(X11) ) ),
    inference(resolution,[],[f87,f76])).

fof(f241,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_1 ),
    inference(backward_demodulation,[],[f99,f238])).

fof(f99,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f347,plain,
    ( ~ spl2_8
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl2_8
    | spl2_12 ),
    inference(subsumption_resolution,[],[f345,f246])).

fof(f246,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f244])).

fof(f345,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f212,f238])).

fof(f212,plain,
    ( v1_relat_1(k2_funct_2(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl2_8
  <=> v1_relat_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f342,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | spl2_8 ),
    inference(subsumption_resolution,[],[f340,f66])).

fof(f340,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl2_8 ),
    inference(subsumption_resolution,[],[f314,f239])).

fof(f239,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl2_8 ),
    inference(backward_demodulation,[],[f213,f238])).

fof(f213,plain,
    ( ~ v1_relat_1(k2_funct_2(sK0,sK1))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f211])).

fof(f314,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f302,f62])).

fof(f104,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f88,f101,f97])).

fof(f88,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f57,f58,f58])).

fof(f57,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:08:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (12841)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (12849)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (12834)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (12826)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12842)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (12831)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (12820)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (12836)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (12828)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (12823)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (12824)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (12830)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (12821)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (12835)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (12836)Refutation not found, incomplete strategy% (12836)------------------------------
% 0.21/0.55  % (12836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12837)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (12844)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (12836)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12836)Memory used [KB]: 10746
% 0.21/0.55  % (12836)Time elapsed: 0.133 s
% 0.21/0.55  % (12836)------------------------------
% 0.21/0.55  % (12836)------------------------------
% 0.21/0.55  % (12822)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (12846)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (12825)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (12847)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (12827)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (12838)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (12839)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (12845)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (12848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (12843)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (12829)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.57/0.57  % (12840)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.57/0.57  % (12826)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f929,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(avatar_sat_refutation,[],[f104,f342,f347,f922,f926])).
% 1.57/0.57  fof(f926,plain,(
% 1.57/0.57    spl2_2),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f925])).
% 1.57/0.57  fof(f925,plain,(
% 1.57/0.57    $false | spl2_2),
% 1.57/0.57    inference(subsumption_resolution,[],[f924,f129])).
% 1.57/0.57  fof(f129,plain,(
% 1.57/0.57    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.57/0.57    inference(resolution,[],[f95,f89])).
% 1.57/0.57  fof(f89,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.57/0.57    inference(definition_unfolding,[],[f60,f58])).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,axiom,(
% 1.57/0.57    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.57/0.57  fof(f60,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,axiom,(
% 1.57/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.57/0.57  fof(f95,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.57/0.57    inference(duplicate_literal_removal,[],[f94])).
% 1.57/0.57  fof(f94,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(equality_resolution,[],[f86])).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f52])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(nnf_transformation,[],[f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(flattening,[],[f43])).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.57    inference(ennf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.57/0.57  fof(f924,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl2_2),
% 1.57/0.57    inference(forward_demodulation,[],[f923,f371])).
% 1.57/0.57  fof(f371,plain,(
% 1.57/0.57    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.57/0.57    inference(forward_demodulation,[],[f370,f172])).
% 1.57/0.57  fof(f172,plain,(
% 1.57/0.57    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 1.57/0.57    inference(backward_demodulation,[],[f155,f171])).
% 1.57/0.57  fof(f171,plain,(
% 1.57/0.57    sK0 = k2_relat_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f170,f107])).
% 1.57/0.57  fof(f107,plain,(
% 1.57/0.57    v1_relat_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f105,f66])).
% 1.57/0.57  fof(f66,plain,(
% 1.57/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.57/0.57  fof(f105,plain,(
% 1.57/0.57    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.57/0.57    inference(resolution,[],[f62,f56])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.57    inference(cnf_transformation,[],[f48])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f47])).
% 1.57/0.57  fof(f47,plain,(
% 1.57/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.57/0.57    inference(flattening,[],[f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.57/0.57    inference(negated_conjecture,[],[f19])).
% 1.57/0.57  fof(f19,conjecture,(
% 1.57/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.57/0.57  fof(f170,plain,(
% 1.57/0.57    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f169,f115])).
% 1.57/0.57  fof(f115,plain,(
% 1.57/0.57    v5_relat_1(sK1,sK0)),
% 1.57/0.57    inference(resolution,[],[f81,f56])).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f40])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.57/0.57  fof(f169,plain,(
% 1.57/0.57    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f168,f70])).
% 1.57/0.57  fof(f70,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.57    inference(nnf_transformation,[],[f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.57    inference(flattening,[],[f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.57/0.57  fof(f168,plain,(
% 1.57/0.57    v2_funct_2(sK1,sK0)),
% 1.57/0.57    inference(subsumption_resolution,[],[f167,f53])).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    v1_funct_1(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f48])).
% 1.57/0.57  fof(f167,plain,(
% 1.57/0.57    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.57/0.57    inference(subsumption_resolution,[],[f165,f55])).
% 1.57/0.57  fof(f55,plain,(
% 1.57/0.57    v3_funct_2(sK1,sK0,sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f48])).
% 1.57/0.57  fof(f165,plain,(
% 1.57/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.57/0.57    inference(resolution,[],[f84,f56])).
% 1.57/0.57  fof(f84,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f42])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(flattening,[],[f41])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.57/0.57  fof(f155,plain,(
% 1.57/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))),
% 1.57/0.57    inference(subsumption_resolution,[],[f154,f107])).
% 1.57/0.57  fof(f154,plain,(
% 1.57/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f152,f53])).
% 1.57/0.57  fof(f152,plain,(
% 1.57/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f151,f64])).
% 1.57/0.57  fof(f64,plain,(
% 1.57/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.57/0.57  fof(f151,plain,(
% 1.57/0.57    v2_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f150,f53])).
% 1.57/0.57  fof(f150,plain,(
% 1.57/0.57    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f148,f55])).
% 1.57/0.57  fof(f148,plain,(
% 1.57/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f83,f56])).
% 1.57/0.57  fof(f83,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f42])).
% 1.57/0.57  fof(f370,plain,(
% 1.57/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f366,f240])).
% 1.57/0.57  fof(f240,plain,(
% 1.57/0.57    v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.57    inference(backward_demodulation,[],[f208,f238])).
% 1.57/0.57  fof(f238,plain,(
% 1.57/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f237,f53])).
% 1.57/0.57  fof(f237,plain,(
% 1.57/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f236,f54])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    v1_funct_2(sK1,sK0,sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f48])).
% 1.57/0.57  fof(f236,plain,(
% 1.57/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f234,f55])).
% 1.57/0.57  fof(f234,plain,(
% 1.57/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f72,f56])).
% 1.57/0.57  fof(f72,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.57/0.57    inference(flattening,[],[f36])).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f17])).
% 1.57/0.57  fof(f17,axiom,(
% 1.57/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.57/0.57  fof(f208,plain,(
% 1.57/0.57    v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.57/0.57    inference(subsumption_resolution,[],[f207,f53])).
% 1.57/0.57  fof(f207,plain,(
% 1.57/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f206,f54])).
% 1.57/0.57  fof(f206,plain,(
% 1.57/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f204,f55])).
% 1.57/0.57  fof(f204,plain,(
% 1.57/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f73,f56])).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.57/0.57    inference(flattening,[],[f38])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,axiom,(
% 1.57/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.57/0.57  fof(f366,plain,(
% 1.57/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.57    inference(resolution,[],[f354,f302])).
% 1.57/0.57  fof(f302,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.57    inference(subsumption_resolution,[],[f301,f53])).
% 1.57/0.57  fof(f301,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f300,f54])).
% 1.57/0.57  fof(f300,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f299,f55])).
% 1.57/0.57  fof(f299,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f281,f56])).
% 1.57/0.57  fof(f281,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(superposition,[],[f76,f238])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f39])).
% 1.57/0.57  fof(f354,plain,(
% 1.57/0.57    ( ! [X14,X12,X13] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | k1_partfun1(X12,X13,sK0,sK0,X14,sK1) = k5_relat_1(X14,sK1) | ~v1_funct_1(X14)) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f351,f53])).
% 1.57/0.57  fof(f351,plain,(
% 1.57/0.57    ( ! [X14,X12,X13] : (k1_partfun1(X12,X13,sK0,sK0,X14,sK1) = k5_relat_1(X14,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_1(X14)) )),
% 1.57/0.57    inference(resolution,[],[f87,f56])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f46])).
% 1.57/0.57  fof(f46,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.57/0.57    inference(flattening,[],[f45])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.57/0.57    inference(ennf_transformation,[],[f16])).
% 1.57/0.57  fof(f16,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.57/0.57  fof(f923,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_2),
% 1.57/0.57    inference(forward_demodulation,[],[f103,f238])).
% 1.57/0.57  fof(f103,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl2_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f101])).
% 1.57/0.57  fof(f101,plain,(
% 1.57/0.57    spl2_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.57/0.57  fof(f922,plain,(
% 1.57/0.57    spl2_1 | ~spl2_12),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f921])).
% 1.57/0.57  fof(f921,plain,(
% 1.57/0.57    $false | (spl2_1 | ~spl2_12)),
% 1.57/0.57    inference(subsumption_resolution,[],[f920,f129])).
% 1.57/0.57  fof(f920,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | (spl2_1 | ~spl2_12)),
% 1.57/0.57    inference(backward_demodulation,[],[f241,f900])).
% 1.57/0.57  fof(f900,plain,(
% 1.57/0.57    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | ~spl2_12),
% 1.57/0.57    inference(forward_demodulation,[],[f899,f699])).
% 1.57/0.57  fof(f699,plain,(
% 1.57/0.57    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~spl2_12),
% 1.57/0.57    inference(backward_demodulation,[],[f157,f694])).
% 1.57/0.57  fof(f694,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK1) | ~spl2_12),
% 1.57/0.57    inference(forward_demodulation,[],[f693,f378])).
% 1.57/0.57  fof(f378,plain,(
% 1.57/0.57    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~spl2_12),
% 1.57/0.57    inference(subsumption_resolution,[],[f377,f245])).
% 1.57/0.57  fof(f245,plain,(
% 1.57/0.57    v1_relat_1(k2_funct_1(sK1)) | ~spl2_12),
% 1.57/0.57    inference(avatar_component_clause,[],[f244])).
% 1.57/0.57  fof(f244,plain,(
% 1.57/0.57    spl2_12 <=> v1_relat_1(k2_funct_1(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.57/0.57  fof(f377,plain,(
% 1.57/0.57    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.57/0.57    inference(subsumption_resolution,[],[f376,f308])).
% 1.57/0.57  fof(f308,plain,(
% 1.57/0.57    v5_relat_1(k2_funct_1(sK1),sK0)),
% 1.57/0.57    inference(resolution,[],[f302,f81])).
% 1.57/0.57  fof(f376,plain,(
% 1.57/0.57    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v5_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.57/0.57    inference(resolution,[],[f325,f70])).
% 1.57/0.57  fof(f325,plain,(
% 1.57/0.57    v2_funct_2(k2_funct_1(sK1),sK0)),
% 1.57/0.57    inference(subsumption_resolution,[],[f324,f240])).
% 1.57/0.57  fof(f324,plain,(
% 1.57/0.57    ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_2(k2_funct_1(sK1),sK0)),
% 1.57/0.57    inference(subsumption_resolution,[],[f305,f267])).
% 1.57/0.57  fof(f267,plain,(
% 1.57/0.57    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f266,f238])).
% 1.57/0.57  fof(f266,plain,(
% 1.57/0.57    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 1.57/0.57    inference(subsumption_resolution,[],[f265,f53])).
% 1.57/0.57  fof(f265,plain,(
% 1.57/0.57    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f264,f54])).
% 1.57/0.57  fof(f264,plain,(
% 1.57/0.57    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f262,f55])).
% 1.57/0.57  fof(f262,plain,(
% 1.57/0.57    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f75,f56])).
% 1.57/0.57  fof(f75,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f39])).
% 1.57/0.57  fof(f305,plain,(
% 1.57/0.57    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_2(k2_funct_1(sK1),sK0)),
% 1.57/0.57    inference(resolution,[],[f302,f84])).
% 1.57/0.57  fof(f693,plain,(
% 1.57/0.57    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~spl2_12),
% 1.57/0.57    inference(forward_demodulation,[],[f690,f261])).
% 1.57/0.57  fof(f261,plain,(
% 1.57/0.57    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f260,f189])).
% 1.57/0.57  fof(f189,plain,(
% 1.57/0.57    sK0 = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f164,f171])).
% 1.57/0.57  fof(f164,plain,(
% 1.57/0.57    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f163,f110])).
% 1.57/0.57  fof(f110,plain,(
% 1.57/0.57    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f61,f107])).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.57/0.57  fof(f163,plain,(
% 1.57/0.57    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 1.57/0.57    inference(subsumption_resolution,[],[f162,f107])).
% 1.57/0.57  fof(f162,plain,(
% 1.57/0.57    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f158,f53])).
% 1.57/0.57  fof(f158,plain,(
% 1.57/0.57    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(resolution,[],[f68,f92])).
% 1.57/0.57  fof(f92,plain,(
% 1.57/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f78])).
% 1.57/0.57  fof(f78,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.57/0.57    inference(cnf_transformation,[],[f51])).
% 1.57/0.57  fof(f51,plain,(
% 1.57/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.57    inference(flattening,[],[f50])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.57    inference(nnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.57/0.57    inference(flattening,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.57/0.57  fof(f260,plain,(
% 1.57/0.57    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 1.57/0.57    inference(subsumption_resolution,[],[f259,f107])).
% 1.57/0.57  fof(f259,plain,(
% 1.57/0.57    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f258,f53])).
% 1.57/0.57  fof(f258,plain,(
% 1.57/0.57    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f188,f151])).
% 1.57/0.57  fof(f188,plain,(
% 1.57/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(resolution,[],[f65,f92])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).
% 1.57/0.57  fof(f690,plain,(
% 1.57/0.57    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),sK0) | ~spl2_12),
% 1.57/0.57    inference(superposition,[],[f355,f375])).
% 1.57/0.57  fof(f375,plain,(
% 1.57/0.57    k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0) | ~spl2_12),
% 1.57/0.57    inference(subsumption_resolution,[],[f374,f245])).
% 1.57/0.57  fof(f374,plain,(
% 1.57/0.57    k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.57/0.57    inference(resolution,[],[f309,f69])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.57    inference(flattening,[],[f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.57/0.57  fof(f309,plain,(
% 1.57/0.57    v4_relat_1(k2_funct_1(sK1),sK0)),
% 1.57/0.57    inference(resolution,[],[f302,f80])).
% 1.57/0.57  fof(f80,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f40])).
% 1.57/0.57  fof(f355,plain,(
% 1.57/0.57    ( ! [X0] : (k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(k2_funct_1(sK1),X0)) ) | ~spl2_12),
% 1.57/0.57    inference(resolution,[],[f245,f67])).
% 1.57/0.57  fof(f67,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.57/0.57  fof(f157,plain,(
% 1.57/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.57/0.57    inference(subsumption_resolution,[],[f156,f107])).
% 1.57/0.57  fof(f156,plain,(
% 1.57/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(subsumption_resolution,[],[f153,f53])).
% 1.57/0.57  fof(f153,plain,(
% 1.57/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f151,f63])).
% 1.57/0.57  fof(f63,plain,(
% 1.57/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f899,plain,(
% 1.57/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 1.57/0.57    inference(subsumption_resolution,[],[f894,f53])).
% 1.57/0.57  fof(f894,plain,(
% 1.57/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 1.57/0.57    inference(resolution,[],[f735,f56])).
% 1.57/0.57  fof(f735,plain,(
% 1.57/0.57    ( ! [X17,X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_1(sK1)) = k5_relat_1(X15,k2_funct_1(sK1)) | ~v1_funct_1(X15)) )),
% 1.57/0.57    inference(forward_demodulation,[],[f734,f238])).
% 1.57/0.57  fof(f734,plain,(
% 1.57/0.57    ( ! [X17,X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~v1_funct_1(X15) | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1))) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f733,f53])).
% 1.57/0.57  fof(f733,plain,(
% 1.57/0.57    ( ! [X17,X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~v1_funct_1(X15) | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f732,f54])).
% 1.57/0.57  fof(f732,plain,(
% 1.57/0.57    ( ! [X17,X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~v1_funct_1(X15) | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f721,f55])).
% 1.57/0.57  fof(f721,plain,(
% 1.57/0.57    ( ! [X17,X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~v1_funct_1(X15) | k1_partfun1(X16,X17,sK0,sK0,X15,k2_funct_2(sK0,sK1)) = k5_relat_1(X15,k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.57/0.57    inference(resolution,[],[f353,f56])).
% 1.57/0.57  fof(f353,plain,(
% 1.57/0.57    ( ! [X10,X8,X7,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X10) | k1_partfun1(X7,X8,X9,X9,X10,k2_funct_2(X9,X11)) = k5_relat_1(X10,k2_funct_2(X9,X11)) | ~v3_funct_2(X11,X9,X9) | ~v1_funct_2(X11,X9,X9) | ~v1_funct_1(X11)) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f350,f73])).
% 1.57/0.57  fof(f350,plain,(
% 1.57/0.57    ( ! [X10,X8,X7,X11,X9] : (k1_partfun1(X7,X8,X9,X9,X10,k2_funct_2(X9,X11)) = k5_relat_1(X10,k2_funct_2(X9,X11)) | ~v1_funct_1(k2_funct_2(X9,X11)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) | ~v3_funct_2(X11,X9,X9) | ~v1_funct_2(X11,X9,X9) | ~v1_funct_1(X11)) )),
% 1.57/0.57    inference(resolution,[],[f87,f76])).
% 1.57/0.57  fof(f241,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_1),
% 1.57/0.57    inference(backward_demodulation,[],[f99,f238])).
% 1.57/0.57  fof(f99,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl2_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f97])).
% 1.57/0.57  fof(f97,plain,(
% 1.57/0.57    spl2_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.57/0.57  fof(f347,plain,(
% 1.57/0.57    ~spl2_8 | spl2_12),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f346])).
% 1.57/0.57  fof(f346,plain,(
% 1.57/0.57    $false | (~spl2_8 | spl2_12)),
% 1.57/0.57    inference(subsumption_resolution,[],[f345,f246])).
% 1.57/0.57  fof(f246,plain,(
% 1.57/0.57    ~v1_relat_1(k2_funct_1(sK1)) | spl2_12),
% 1.57/0.57    inference(avatar_component_clause,[],[f244])).
% 1.57/0.57  fof(f345,plain,(
% 1.57/0.57    v1_relat_1(k2_funct_1(sK1)) | ~spl2_8),
% 1.57/0.57    inference(forward_demodulation,[],[f212,f238])).
% 1.57/0.57  fof(f212,plain,(
% 1.57/0.57    v1_relat_1(k2_funct_2(sK0,sK1)) | ~spl2_8),
% 1.57/0.57    inference(avatar_component_clause,[],[f211])).
% 1.57/0.57  fof(f211,plain,(
% 1.57/0.57    spl2_8 <=> v1_relat_1(k2_funct_2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.57/0.57  fof(f342,plain,(
% 1.57/0.57    spl2_8),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f341])).
% 1.57/0.57  fof(f341,plain,(
% 1.57/0.57    $false | spl2_8),
% 1.57/0.57    inference(subsumption_resolution,[],[f340,f66])).
% 1.57/0.57  fof(f340,plain,(
% 1.57/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl2_8),
% 1.57/0.57    inference(subsumption_resolution,[],[f314,f239])).
% 1.57/0.57  fof(f239,plain,(
% 1.57/0.57    ~v1_relat_1(k2_funct_1(sK1)) | spl2_8),
% 1.57/0.57    inference(backward_demodulation,[],[f213,f238])).
% 1.57/0.57  fof(f213,plain,(
% 1.57/0.57    ~v1_relat_1(k2_funct_2(sK0,sK1)) | spl2_8),
% 1.57/0.57    inference(avatar_component_clause,[],[f211])).
% 1.57/0.57  fof(f314,plain,(
% 1.57/0.57    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.57/0.57    inference(resolution,[],[f302,f62])).
% 1.57/0.57  fof(f104,plain,(
% 1.57/0.57    ~spl2_1 | ~spl2_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f88,f101,f97])).
% 1.57/0.57  fof(f88,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.57/0.57    inference(definition_unfolding,[],[f57,f58,f58])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.57/0.57    inference(cnf_transformation,[],[f48])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (12826)------------------------------
% 1.57/0.57  % (12826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (12826)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (12826)Memory used [KB]: 11385
% 1.57/0.57  % (12826)Time elapsed: 0.093 s
% 1.57/0.57  % (12826)------------------------------
% 1.57/0.57  % (12826)------------------------------
% 1.57/0.57  % (12819)Success in time 0.207 s
%------------------------------------------------------------------------------
