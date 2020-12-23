%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:59 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  169 (1508 expanded)
%              Number of leaves         :   20 ( 367 expanded)
%              Depth                    :   22
%              Number of atoms          :  485 (7820 expanded)
%              Number of equality atoms :   94 ( 244 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(subsumption_resolution,[],[f467,f107])).

fof(f107,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(resolution,[],[f89,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f58,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(condensation,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f467,plain,(
    ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f365,f466])).

fof(f466,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f377,f152])).

fof(f152,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f151,f134])).

fof(f134,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f48])).

fof(f48,plain,
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

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f133,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f132,f55])).

fof(f55,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f132,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f131,f56])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f131,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f151,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f150,f53])).

fof(f150,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f149,f55])).

fof(f149,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f148,f56])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f75,f54])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

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

fof(f377,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,sK1,k2_funct_1(sK1)) ) ),
    inference(resolution,[],[f350,f56])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(backward_demodulation,[],[f286,f349])).

fof(f349,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f348,f224])).

fof(f224,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f223,f196])).

fof(f196,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f195,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f195,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f152,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f223,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f222,f193])).

fof(f193,plain,(
    v5_relat_1(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f152,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f222,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f189,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f189,plain,(
    v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f188,f152])).

fof(f188,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f186,f135])).

fof(f135,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f121,f134])).

fof(f121,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f120,f53])).

fof(f120,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f119,f55])).

fof(f119,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f118,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f186,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f147,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f147,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f146,f134])).

fof(f146,plain,(
    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f145,f53])).

fof(f145,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f144,f55])).

fof(f144,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f143,f56])).

fof(f143,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f348,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f346,f276])).

fof(f276,plain,(
    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f275,f198])).

fof(f198,plain,(
    sK0 = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f197,f159])).

fof(f159,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f98,f156])).

fof(f156,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f155,f95])).

fof(f95,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f93,f65])).

fof(f93,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f61,f56])).

fof(f155,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f102])).

fof(f102,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f80,f56])).

fof(f154,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f117,f69])).

fof(f117,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f116,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f115,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f83,f55])).

fof(f98,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(resolution,[],[f60,f95])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f197,plain,(
    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f158,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f114,f156])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f113,f95])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f67,f53])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f275,plain,(
    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(resolution,[],[f126,f87])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f125,f95])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f122,f53])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f112,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f111,f56])).

fof(f111,plain,
    ( v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f110,f53])).

fof(f110,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f346,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(superposition,[],[f216,f230])).

fof(f230,plain,(
    k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f229,f196])).

fof(f229,plain,
    ( k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f194,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f194,plain,(
    v4_relat_1(k2_funct_1(sK1),sK0) ),
    inference(resolution,[],[f152,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f216,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK1),X0) = k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0)) ),
    inference(resolution,[],[f196,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f286,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(forward_demodulation,[],[f283,f130])).

fof(f130,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f129,f95])).

fof(f129,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f124,f53])).

fof(f124,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f112,f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f283,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f160,f53])).

fof(f160,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k1_partfun1(X2,X3,X0,X1,X4,k2_funct_1(sK1)) = k5_relat_1(X4,k2_funct_1(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f135,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f365,plain,(
    ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f364,f107])).

fof(f364,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f137,f363])).

fof(f363,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f282,f56])).

fof(f282,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) ) ),
    inference(resolution,[],[f201,f152])).

fof(f201,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k6_relat_1(sK0) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(forward_demodulation,[],[f200,f157])).

fof(f157,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f128,f156])).

fof(f128,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f127,f95])).

fof(f127,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f123,f53])).

fof(f123,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f112,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f200,plain,(
    ! [X6,X4,X7,X5] :
      ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1)
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f153,f135])).

fof(f153,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f85,f53])).

fof(f137,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f136,f134])).

fof(f136,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f91,f134])).

fof(f91,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f90,f58])).

fof(f90,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f57,f58])).

fof(f57,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (31038)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (31040)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.52  % (31041)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (31058)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.23/0.52  % (31050)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.23/0.52  % (31036)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.52  % (31052)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.23/0.53  % (31055)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.53  % (31042)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.53  % (31044)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.23/0.53  % (31047)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.53  % (31037)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.53  % (31049)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.53  % (31039)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.54  % (31064)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (31060)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (31062)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % (31046)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.54  % (31035)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.54  % (31059)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (31063)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (31056)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.55  % (31054)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.55  % (31061)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.55  % (31057)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.55  % (31045)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.55  % (31053)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.55  % (31051)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.56  % (31043)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.56  % (31048)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.56  % (31042)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f468,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(subsumption_resolution,[],[f467,f107])).
% 1.34/0.56  fof(f107,plain,(
% 1.34/0.56    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.34/0.56    inference(resolution,[],[f89,f92])).
% 1.34/0.56  fof(f92,plain,(
% 1.34/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.34/0.56    inference(forward_demodulation,[],[f59,f58])).
% 1.34/0.56  fof(f58,plain,(
% 1.34/0.56    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f18])).
% 1.34/0.56  fof(f18,axiom,(
% 1.34/0.56    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.34/0.56  fof(f59,plain,(
% 1.34/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f21])).
% 1.34/0.56  fof(f21,plain,(
% 1.34/0.56    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.34/0.56    inference(pure_predicate_removal,[],[f15])).
% 1.34/0.56  fof(f15,axiom,(
% 1.34/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.34/0.56  fof(f89,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 1.34/0.56    inference(condensation,[],[f84])).
% 1.34/0.56  fof(f84,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f45])).
% 1.34/0.56  fof(f45,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.56    inference(flattening,[],[f44])).
% 1.34/0.56  fof(f44,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.34/0.56    inference(ennf_transformation,[],[f11])).
% 1.34/0.56  fof(f11,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.34/0.56  fof(f467,plain,(
% 1.34/0.56    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 1.34/0.56    inference(backward_demodulation,[],[f365,f466])).
% 1.34/0.56  fof(f466,plain,(
% 1.34/0.56    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 1.34/0.56    inference(resolution,[],[f377,f152])).
% 1.34/0.56  fof(f152,plain,(
% 1.34/0.56    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.56    inference(forward_demodulation,[],[f151,f134])).
% 1.34/0.56  fof(f134,plain,(
% 1.34/0.56    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.34/0.56    inference(subsumption_resolution,[],[f133,f53])).
% 1.34/0.56  fof(f53,plain,(
% 1.34/0.56    v1_funct_1(sK1)),
% 1.34/0.56    inference(cnf_transformation,[],[f49])).
% 1.34/0.56  fof(f49,plain,(
% 1.34/0.56    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f48])).
% 1.34/0.56  fof(f48,plain,(
% 1.34/0.56    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f23,plain,(
% 1.34/0.56    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.34/0.56    inference(flattening,[],[f22])).
% 1.34/0.56  fof(f22,plain,(
% 1.34/0.56    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.34/0.56    inference(ennf_transformation,[],[f20])).
% 1.34/0.56  fof(f20,negated_conjecture,(
% 1.34/0.56    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.34/0.56    inference(negated_conjecture,[],[f19])).
% 1.34/0.56  fof(f19,conjecture,(
% 1.34/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.34/0.56  fof(f133,plain,(
% 1.34/0.56    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.34/0.56    inference(subsumption_resolution,[],[f132,f55])).
% 1.34/0.56  fof(f55,plain,(
% 1.34/0.56    v3_funct_2(sK1,sK0,sK0)),
% 1.34/0.56    inference(cnf_transformation,[],[f49])).
% 1.34/0.56  fof(f132,plain,(
% 1.34/0.56    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.34/0.56    inference(subsumption_resolution,[],[f131,f56])).
% 1.34/0.56  fof(f56,plain,(
% 1.34/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.56    inference(cnf_transformation,[],[f49])).
% 1.34/0.56  fof(f131,plain,(
% 1.34/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.34/0.56    inference(resolution,[],[f71,f54])).
% 1.34/0.56  fof(f54,plain,(
% 1.34/0.56    v1_funct_2(sK1,sK0,sK0)),
% 1.34/0.56    inference(cnf_transformation,[],[f49])).
% 1.34/0.56  fof(f71,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f38])).
% 1.34/0.56  fof(f38,plain,(
% 1.34/0.56    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.34/0.56    inference(flattening,[],[f37])).
% 1.34/0.56  fof(f37,plain,(
% 1.34/0.56    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.34/0.56    inference(ennf_transformation,[],[f17])).
% 1.34/0.56  fof(f17,axiom,(
% 1.34/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.34/0.56  fof(f151,plain,(
% 1.34/0.56    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.56    inference(subsumption_resolution,[],[f150,f53])).
% 1.34/0.56  fof(f150,plain,(
% 1.34/0.56    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.34/0.56    inference(subsumption_resolution,[],[f149,f55])).
% 1.34/0.56  fof(f149,plain,(
% 1.34/0.56    ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.34/0.56    inference(subsumption_resolution,[],[f148,f56])).
% 1.34/0.56  fof(f148,plain,(
% 1.34/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.34/0.56    inference(resolution,[],[f75,f54])).
% 1.34/0.57  fof(f75,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f40])).
% 1.34/0.57  fof(f40,plain,(
% 1.34/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.34/0.57    inference(flattening,[],[f39])).
% 1.34/0.57  fof(f39,plain,(
% 1.34/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.34/0.57    inference(ennf_transformation,[],[f14])).
% 1.34/0.57  fof(f14,axiom,(
% 1.34/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.34/0.57  fof(f377,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,sK1,k2_funct_1(sK1))) )),
% 1.34/0.57    inference(resolution,[],[f350,f56])).
% 1.34/0.57  fof(f350,plain,(
% 1.34/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.34/0.57    inference(backward_demodulation,[],[f286,f349])).
% 1.34/0.57  fof(f349,plain,(
% 1.34/0.57    sK0 = k1_relat_1(sK1)),
% 1.34/0.57    inference(forward_demodulation,[],[f348,f224])).
% 1.34/0.57  fof(f224,plain,(
% 1.34/0.57    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f223,f196])).
% 1.34/0.57  fof(f196,plain,(
% 1.34/0.57    v1_relat_1(k2_funct_1(sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f195,f65])).
% 1.34/0.57  fof(f65,plain,(
% 1.34/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f3])).
% 1.34/0.57  fof(f3,axiom,(
% 1.34/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.57  fof(f195,plain,(
% 1.34/0.57    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.34/0.57    inference(resolution,[],[f152,f61])).
% 1.34/0.57  fof(f61,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f25])).
% 1.34/0.57  fof(f25,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(ennf_transformation,[],[f2])).
% 1.34/0.57  fof(f2,axiom,(
% 1.34/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.57  fof(f223,plain,(
% 1.34/0.57    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f222,f193])).
% 1.34/0.57  fof(f193,plain,(
% 1.34/0.57    v5_relat_1(k2_funct_1(sK1),sK0)),
% 1.34/0.57    inference(resolution,[],[f152,f80])).
% 1.34/0.57  fof(f80,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f41])).
% 1.34/0.57  fof(f41,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.57    inference(ennf_transformation,[],[f10])).
% 1.34/0.57  fof(f10,axiom,(
% 1.34/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.57  fof(f222,plain,(
% 1.34/0.57    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v5_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.34/0.57    inference(resolution,[],[f189,f69])).
% 1.34/0.57  fof(f69,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f50])).
% 1.34/0.57  fof(f50,plain,(
% 1.34/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.57    inference(nnf_transformation,[],[f36])).
% 1.34/0.57  fof(f36,plain,(
% 1.34/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.57    inference(flattening,[],[f35])).
% 1.34/0.57  fof(f35,plain,(
% 1.34/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.57    inference(ennf_transformation,[],[f13])).
% 1.34/0.57  fof(f13,axiom,(
% 1.34/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.34/0.57  fof(f189,plain,(
% 1.34/0.57    v2_funct_2(k2_funct_1(sK1),sK0)),
% 1.34/0.57    inference(subsumption_resolution,[],[f188,f152])).
% 1.34/0.57  fof(f188,plain,(
% 1.34/0.57    v2_funct_2(k2_funct_1(sK1),sK0) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.57    inference(subsumption_resolution,[],[f186,f135])).
% 1.34/0.57  fof(f135,plain,(
% 1.34/0.57    v1_funct_1(k2_funct_1(sK1))),
% 1.34/0.57    inference(backward_demodulation,[],[f121,f134])).
% 1.34/0.57  fof(f121,plain,(
% 1.34/0.57    v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f120,f53])).
% 1.34/0.57  fof(f120,plain,(
% 1.34/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f119,f55])).
% 1.34/0.57  fof(f119,plain,(
% 1.34/0.57    ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f118,f56])).
% 1.34/0.57  fof(f118,plain,(
% 1.34/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 1.34/0.57    inference(resolution,[],[f72,f54])).
% 1.34/0.57  fof(f72,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1)) | ~v1_funct_1(X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f40])).
% 1.34/0.57  fof(f186,plain,(
% 1.34/0.57    v2_funct_2(k2_funct_1(sK1),sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.57    inference(resolution,[],[f147,f83])).
% 1.34/0.57  fof(f83,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f43])).
% 1.34/0.57  fof(f43,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.57    inference(flattening,[],[f42])).
% 1.34/0.57  fof(f42,plain,(
% 1.34/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.57    inference(ennf_transformation,[],[f12])).
% 1.34/0.57  fof(f12,axiom,(
% 1.34/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.34/0.57  fof(f147,plain,(
% 1.34/0.57    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.34/0.57    inference(forward_demodulation,[],[f146,f134])).
% 1.34/0.57  fof(f146,plain,(
% 1.34/0.57    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 1.34/0.57    inference(subsumption_resolution,[],[f145,f53])).
% 1.34/0.57  fof(f145,plain,(
% 1.34/0.57    v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f144,f55])).
% 1.34/0.57  fof(f144,plain,(
% 1.34/0.57    ~v3_funct_2(sK1,sK0,sK0) | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f143,f56])).
% 1.34/0.57  fof(f143,plain,(
% 1.34/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.34/0.57    inference(resolution,[],[f74,f54])).
% 1.34/0.57  fof(f74,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_1(X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f40])).
% 1.34/0.57  fof(f348,plain,(
% 1.34/0.57    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 1.34/0.57    inference(forward_demodulation,[],[f346,f276])).
% 1.34/0.57  fof(f276,plain,(
% 1.34/0.57    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),sK0)),
% 1.34/0.57    inference(forward_demodulation,[],[f275,f198])).
% 1.34/0.57  fof(f198,plain,(
% 1.34/0.57    sK0 = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.34/0.57    inference(forward_demodulation,[],[f197,f159])).
% 1.34/0.57  fof(f159,plain,(
% 1.34/0.57    k1_relat_1(sK1) = k10_relat_1(sK1,sK0)),
% 1.34/0.57    inference(backward_demodulation,[],[f98,f156])).
% 1.34/0.57  fof(f156,plain,(
% 1.34/0.57    sK0 = k2_relat_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f155,f95])).
% 1.34/0.57  fof(f95,plain,(
% 1.34/0.57    v1_relat_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f93,f65])).
% 1.34/0.57  fof(f93,plain,(
% 1.34/0.57    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.34/0.57    inference(resolution,[],[f61,f56])).
% 1.34/0.57  fof(f155,plain,(
% 1.34/0.57    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f154,f102])).
% 1.34/0.57  fof(f102,plain,(
% 1.34/0.57    v5_relat_1(sK1,sK0)),
% 1.34/0.57    inference(resolution,[],[f80,f56])).
% 1.34/0.57  fof(f154,plain,(
% 1.34/0.57    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.34/0.57    inference(resolution,[],[f117,f69])).
% 1.34/0.57  fof(f117,plain,(
% 1.34/0.57    v2_funct_2(sK1,sK0)),
% 1.34/0.57    inference(subsumption_resolution,[],[f116,f56])).
% 1.34/0.57  fof(f116,plain,(
% 1.34/0.57    v2_funct_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.57    inference(subsumption_resolution,[],[f115,f53])).
% 1.34/0.57  fof(f115,plain,(
% 1.34/0.57    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.57    inference(resolution,[],[f83,f55])).
% 1.34/0.57  fof(f98,plain,(
% 1.34/0.57    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 1.34/0.57    inference(resolution,[],[f60,f95])).
% 1.34/0.57  fof(f60,plain,(
% 1.34/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f24])).
% 1.34/0.57  fof(f24,plain,(
% 1.34/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(ennf_transformation,[],[f5])).
% 1.34/0.57  fof(f5,axiom,(
% 1.34/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.34/0.57  fof(f197,plain,(
% 1.34/0.57    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 1.34/0.57    inference(resolution,[],[f158,f87])).
% 1.34/0.57  fof(f87,plain,(
% 1.34/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.57    inference(equality_resolution,[],[f77])).
% 1.34/0.57  fof(f77,plain,(
% 1.34/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.57    inference(cnf_transformation,[],[f52])).
% 1.34/0.57  fof(f52,plain,(
% 1.34/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.57    inference(flattening,[],[f51])).
% 1.34/0.57  fof(f51,plain,(
% 1.34/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.57    inference(nnf_transformation,[],[f1])).
% 1.34/0.57  fof(f1,axiom,(
% 1.34/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.57  fof(f158,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) )),
% 1.34/0.57    inference(backward_demodulation,[],[f114,f156])).
% 1.34/0.57  fof(f114,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f113,f95])).
% 1.34/0.57  fof(f113,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 1.34/0.57    inference(resolution,[],[f67,f53])).
% 1.34/0.57  fof(f67,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f32])).
% 1.34/0.57  fof(f32,plain,(
% 1.34/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.34/0.57    inference(flattening,[],[f31])).
% 1.34/0.57  fof(f31,plain,(
% 1.34/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.34/0.57    inference(ennf_transformation,[],[f7])).
% 1.34/0.57  fof(f7,axiom,(
% 1.34/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.34/0.57  fof(f275,plain,(
% 1.34/0.57    k1_relat_1(sK1) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 1.34/0.57    inference(resolution,[],[f126,f87])).
% 1.34/0.57  fof(f126,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f125,f95])).
% 1.34/0.57  fof(f125,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f122,f53])).
% 1.34/0.57  fof(f122,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.34/0.57    inference(resolution,[],[f112,f64])).
% 1.34/0.57  fof(f64,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v2_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f29])).
% 1.34/0.57  fof(f29,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f28])).
% 1.34/0.57  fof(f28,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f8])).
% 1.34/0.57  fof(f8,axiom,(
% 1.34/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).
% 1.34/0.57  fof(f112,plain,(
% 1.34/0.57    v2_funct_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f111,f56])).
% 1.34/0.57  fof(f111,plain,(
% 1.34/0.57    v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.57    inference(subsumption_resolution,[],[f110,f53])).
% 1.34/0.57  fof(f110,plain,(
% 1.34/0.57    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.57    inference(resolution,[],[f82,f55])).
% 1.34/0.57  fof(f82,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f43])).
% 1.34/0.57  fof(f346,plain,(
% 1.34/0.57    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),sK0)),
% 1.34/0.57    inference(superposition,[],[f216,f230])).
% 1.34/0.57  fof(f230,plain,(
% 1.34/0.57    k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0)),
% 1.34/0.57    inference(subsumption_resolution,[],[f229,f196])).
% 1.34/0.57  fof(f229,plain,(
% 1.34/0.57    k2_funct_1(sK1) = k7_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.34/0.57    inference(resolution,[],[f194,f68])).
% 1.34/0.57  fof(f68,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f34])).
% 1.34/0.57  fof(f34,plain,(
% 1.34/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.57    inference(flattening,[],[f33])).
% 1.34/0.57  fof(f33,plain,(
% 1.34/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.57    inference(ennf_transformation,[],[f6])).
% 1.34/0.57  fof(f6,axiom,(
% 1.34/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.34/0.57  fof(f194,plain,(
% 1.34/0.57    v4_relat_1(k2_funct_1(sK1),sK0)),
% 1.34/0.57    inference(resolution,[],[f152,f79])).
% 1.34/0.57  fof(f79,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f41])).
% 1.34/0.57  fof(f216,plain,(
% 1.34/0.57    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),X0) = k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0))) )),
% 1.34/0.57    inference(resolution,[],[f196,f66])).
% 1.34/0.57  fof(f66,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f30])).
% 1.34/0.57  fof(f30,plain,(
% 1.34/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.57    inference(ennf_transformation,[],[f4])).
% 1.34/0.57  fof(f4,axiom,(
% 1.34/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.34/0.57  fof(f286,plain,(
% 1.34/0.57    ( ! [X2,X0,X3,X1] : (k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.34/0.57    inference(forward_demodulation,[],[f283,f130])).
% 1.34/0.57  fof(f130,plain,(
% 1.34/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f129,f95])).
% 1.34/0.57  fof(f129,plain,(
% 1.34/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f124,f53])).
% 1.34/0.57  fof(f124,plain,(
% 1.34/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.34/0.57    inference(resolution,[],[f112,f62])).
% 1.34/0.57  fof(f62,plain,(
% 1.34/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f27])).
% 1.34/0.57  fof(f27,plain,(
% 1.34/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f26])).
% 1.34/0.57  fof(f26,plain,(
% 1.34/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f9])).
% 1.34/0.57  fof(f9,axiom,(
% 1.34/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.34/0.57  fof(f283,plain,(
% 1.34/0.57    ( ! [X2,X0,X3,X1] : (k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.34/0.57    inference(resolution,[],[f160,f53])).
% 1.34/0.57  fof(f160,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | k1_partfun1(X2,X3,X0,X1,X4,k2_funct_1(sK1)) = k5_relat_1(X4,k2_funct_1(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.57    inference(resolution,[],[f135,f85])).
% 1.34/0.57  fof(f85,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f47])).
% 1.34/0.57  fof(f47,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.34/0.57    inference(flattening,[],[f46])).
% 1.34/0.57  fof(f46,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.34/0.57    inference(ennf_transformation,[],[f16])).
% 1.34/0.57  fof(f16,axiom,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.34/0.57  fof(f365,plain,(
% 1.34/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.34/0.57    inference(subsumption_resolution,[],[f364,f107])).
% 1.34/0.57  fof(f364,plain,(
% 1.34/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.34/0.57    inference(backward_demodulation,[],[f137,f363])).
% 1.34/0.57  fof(f363,plain,(
% 1.34/0.57    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.34/0.57    inference(resolution,[],[f282,f56])).
% 1.34/0.57  fof(f282,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) )),
% 1.34/0.57    inference(resolution,[],[f201,f152])).
% 1.34/0.57  fof(f201,plain,(
% 1.34/0.57    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k6_relat_1(sK0) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 1.34/0.57    inference(forward_demodulation,[],[f200,f157])).
% 1.34/0.57  fof(f157,plain,(
% 1.34/0.57    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 1.34/0.57    inference(backward_demodulation,[],[f128,f156])).
% 1.34/0.57  fof(f128,plain,(
% 1.34/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f127,f95])).
% 1.34/0.57  fof(f127,plain,(
% 1.34/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f123,f53])).
% 1.34/0.57  fof(f123,plain,(
% 1.34/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.34/0.57    inference(resolution,[],[f112,f63])).
% 1.34/0.57  fof(f63,plain,(
% 1.34/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f27])).
% 1.34/0.57  fof(f200,plain,(
% 1.34/0.57    ( ! [X6,X4,X7,X5] : (k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 1.34/0.57    inference(resolution,[],[f153,f135])).
% 1.34/0.57  fof(f153,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.57    inference(resolution,[],[f85,f53])).
% 1.34/0.57  fof(f137,plain,(
% 1.34/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.34/0.57    inference(forward_demodulation,[],[f136,f134])).
% 1.34/0.57  fof(f136,plain,(
% 1.34/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.34/0.57    inference(backward_demodulation,[],[f91,f134])).
% 1.34/0.57  fof(f91,plain,(
% 1.34/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.34/0.57    inference(forward_demodulation,[],[f90,f58])).
% 1.34/0.57  fof(f90,plain,(
% 1.34/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.34/0.57    inference(forward_demodulation,[],[f57,f58])).
% 1.34/0.57  fof(f57,plain,(
% 1.34/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.34/0.57    inference(cnf_transformation,[],[f49])).
% 1.34/0.57  % SZS output end Proof for theBenchmark
% 1.34/0.57  % (31042)------------------------------
% 1.34/0.57  % (31042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.57  % (31042)Termination reason: Refutation
% 1.34/0.57  
% 1.34/0.57  % (31042)Memory used [KB]: 2046
% 1.34/0.57  % (31042)Time elapsed: 0.099 s
% 1.34/0.57  % (31042)------------------------------
% 1.34/0.57  % (31042)------------------------------
% 1.34/0.57  % (31034)Success in time 0.21 s
%------------------------------------------------------------------------------
