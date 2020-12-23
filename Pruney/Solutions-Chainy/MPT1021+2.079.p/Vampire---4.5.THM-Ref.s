%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:02 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  174 (2709 expanded)
%              Number of leaves         :   15 ( 657 expanded)
%              Depth                    :   59
%              Number of atoms          :  680 (15045 expanded)
%              Number of equality atoms :   69 ( 398 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f50,f43,f42,f43,f324])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f323,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f322,f40])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f36])).

fof(f36,plain,
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

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f322,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f321,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f321,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f320,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f320,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f318,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f318,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f317,f125])).

fof(f125,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f124,f50])).

fof(f124,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f105,f43])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | sK0 = k2_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f83,f43])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | sK0 = k2_relat_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f80,f47])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | sK0 = k2_relat_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f79,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f77,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f77,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0) ),
    inference(resolution,[],[f75,f43])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_2(sK1,X1)
      | ~ v3_funct_2(sK1,X0,X1) ) ),
    inference(resolution,[],[f63,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f317,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f316,f40])).

fof(f316,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f315,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f315,plain,(
    ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f314,f94])).

fof(f94,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f93,f40])).

fof(f93,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f92,f41])).

fof(f41,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f90,f43])).

fof(f90,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f54,f87])).

fof(f87,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f314,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f313,f115])).

fof(f115,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f114,f40])).

fof(f114,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f113,f41])).

fof(f113,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f112,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f111,f43])).

fof(f111,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f57,f87])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f313,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f312,f40])).

fof(f312,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f311,f43])).

fof(f311,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f302,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f302,plain,(
    ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f301,f67])).

fof(f301,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f300,f72])).

fof(f300,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f123,f298])).

fof(f298,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f297,f110])).

fof(f110,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f109,f40])).

fof(f109,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f108,f41])).

fof(f108,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f107,f42])).

% (23448)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (23439)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (23435)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (23438)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (23423)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f107,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f106,f43])).

fof(f106,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f56,f87])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f297,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f289,f115])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(k2_funct_1(sK1),X0,X1)
      | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f288,f50])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(k2_funct_1(sK1),X0,X1)
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ) ),
    inference(resolution,[],[f285,f115])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(X2))
      | ~ v3_funct_2(k2_funct_1(sK1),X0,X1)
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f280,f47])).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v3_funct_2(k2_funct_1(sK1),X0,X1)
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f273,f276])).

fof(f276,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f275,f50])).

fof(f275,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f274,f115])).

fof(f274,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(X0))
      | sK0 = k2_relat_1(k2_funct_1(sK1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f135,f115])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | sK0 = k2_relat_1(k2_funct_1(sK1))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f129,f47])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | sK0 = k2_relat_1(k2_funct_1(sK1))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(resolution,[],[f118,f60])).

fof(f118,plain,
    ( ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f117,f51])).

fof(f117,plain,(
    v2_funct_2(k2_funct_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f116,f110])).

fof(f116,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(resolution,[],[f115,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v2_funct_2(k2_funct_1(sK1),X1)
      | ~ v3_funct_2(k2_funct_1(sK1),X0,X1) ) ),
    inference(resolution,[],[f94,f63])).

fof(f273,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v3_funct_2(k2_funct_1(sK1),X0,X1)
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f272,f94])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v3_funct_2(k2_funct_1(sK1),X0,X1)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f261,f62])).

fof(f261,plain,
    ( ~ v2_funct_1(k2_funct_1(sK1))
    | k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f257,f94])).

fof(f257,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ v2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f68,f224])).

fof(f224,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f223,f50])).

fof(f223,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f222,f43])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | sK1 = k2_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f221,f47])).

fof(f221,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f220,f67])).

fof(f220,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f215,f72])).

fof(f215,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f214,f43])).

fof(f214,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f213,f179])).

fof(f179,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f178,f94])).

fof(f178,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f177,f100])).

fof(f100,plain,(
    v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(forward_demodulation,[],[f99,f87])).

fof(f99,plain,(
    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f98,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f97,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f96,f43])).

fof(f96,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f55,f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f177,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f176,f110])).

fof(f176,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f169,f115])).

fof(f169,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f57,f153])).

fof(f153,plain,(
    k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f152,f115])).

fof(f152,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1)) ),
    inference(resolution,[],[f104,f110])).

fof(f104,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f102,f94])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f100,f53])).

fof(f213,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f202,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f202,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_1(k2_funct_1(sK1)))
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f201,f125])).

fof(f201,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_1(k2_funct_1(sK1)))
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f200,f153])).

fof(f200,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f199,f94])).

fof(f199,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f198,f100])).

fof(f198,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f197,f110])).

fof(f197,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f196,f40])).

fof(f196,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f195,f41])).

fof(f195,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f194,f42])).

fof(f194,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f193,f43])).

fof(f193,plain,
    ( r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f148,f115])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | r2_relset_1(X1,X1,X0,k2_funct_2(X1,k2_funct_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v3_funct_2(X0,X1,X1)
      | ~ v1_funct_2(X0,X1,X1)
      | ~ v1_funct_1(X0)
      | ~ r2_relset_1(X1,X1,k6_partfun1(k2_relat_1(X0)),k6_partfun1(X1))
      | ~ v3_funct_2(k2_funct_1(X0),X1,X1)
      | ~ v1_funct_2(k2_funct_1(X0),X1,X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f147,f62])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r2_relset_1(X1,X1,k6_partfun1(k2_relat_1(X0)),k6_partfun1(X1))
      | r2_relset_1(X1,X1,X0,k2_funct_2(X1,k2_funct_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v3_funct_2(X0,X1,X1)
      | ~ v1_funct_2(X0,X1,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v3_funct_2(k2_funct_1(X0),X1,X1)
      | ~ v1_funct_2(k2_funct_1(X0),X1,X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_relset_1(X1,X1,k6_partfun1(k2_relat_1(X0)),k6_partfun1(X1))
      | r2_relset_1(X1,X1,X0,k2_funct_2(X1,k2_funct_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v3_funct_2(X0,X1,X1)
      | ~ v1_funct_2(X0,X1,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v3_funct_2(k2_funct_1(X0),X1,X1)
      | ~ v1_funct_2(k2_funct_1(X0),X1,X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f127,f68])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_relset_1(X0,X0,k5_relat_1(X1,X2),k6_partfun1(X0))
      | r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_relset_1(X0,X0,k5_relat_1(X1,X2),k6_partfun1(X0))
      | r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(superposition,[],[f58,f66])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
      | r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v3_funct_2(X2,X0,X0)
          | ~ v1_funct_2(X2,X0,X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v3_funct_2(X2,X0,X0)
          | ~ v1_funct_2(X2,X0,X0)
          | ~ v1_funct_1(X2) )
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
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f123,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f122,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f121,f43])).

fof(f121,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f120,f94])).

fof(f120,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f119,f115])).

fof(f119,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f89,f66])).

fof(f89,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f88,f87])).

fof(f88,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f44,f87])).

fof(f44,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (23428)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (23424)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.43/0.56  % (23450)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.56  % (23444)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.56  % (23431)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.56  % (23447)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.43/0.56  % (23437)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.56  % (23446)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.56  % (23429)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (23425)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.57  % (23426)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.57/0.57  % (23449)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.57  % (23436)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.57  % (23433)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.57/0.57  % (23427)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.57  % (23441)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.57/0.58  % (23434)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.57/0.58  % (23430)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.58  % (23454)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.58  % (23440)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.58  % (23453)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.58  % (23440)Refutation not found, incomplete strategy% (23440)------------------------------
% 1.57/0.58  % (23440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (23440)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (23440)Memory used [KB]: 10746
% 1.57/0.58  % (23440)Time elapsed: 0.179 s
% 1.57/0.58  % (23440)------------------------------
% 1.57/0.58  % (23440)------------------------------
% 1.57/0.58  % (23442)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.57/0.59  % (23452)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.57/0.59  % (23443)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.57/0.59  % (23451)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.59  % (23447)Refutation found. Thanks to Tanya!
% 1.57/0.59  % SZS status Theorem for theBenchmark
% 1.57/0.59  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f325,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(unit_resulting_resolution,[],[f50,f43,f42,f43,f324])).
% 1.57/0.59  fof(f324,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(sK1,X0,X1) | ~v1_relat_1(X2)) )),
% 1.57/0.59    inference(resolution,[],[f323,f47])).
% 1.57/0.59  fof(f47,plain,(
% 1.57/0.59    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f18])).
% 1.57/0.59  fof(f18,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f1])).
% 1.57/0.59  fof(f1,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.57/0.59  fof(f323,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v3_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(subsumption_resolution,[],[f322,f40])).
% 1.57/0.59  fof(f40,plain,(
% 1.57/0.59    v1_funct_1(sK1)),
% 1.57/0.59    inference(cnf_transformation,[],[f37])).
% 1.57/0.59  fof(f37,plain,(
% 1.57/0.59    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f36])).
% 1.57/0.59  fof(f36,plain,(
% 1.57/0.59    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f17,plain,(
% 1.57/0.59    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.57/0.59    inference(flattening,[],[f16])).
% 1.57/0.59  fof(f16,plain,(
% 1.57/0.59    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f15])).
% 1.57/0.59  fof(f15,negated_conjecture,(
% 1.57/0.59    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.57/0.59    inference(negated_conjecture,[],[f14])).
% 1.57/0.59  fof(f14,conjecture,(
% 1.57/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.57/0.59  fof(f322,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v3_funct_2(sK1,X0,X1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(resolution,[],[f321,f62])).
% 1.57/0.59  fof(f62,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f31])).
% 1.57/0.59  fof(f31,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(flattening,[],[f30])).
% 1.57/0.59  fof(f30,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(ennf_transformation,[],[f7])).
% 1.57/0.59  fof(f7,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.57/0.59  fof(f321,plain,(
% 1.57/0.59    ~v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f320,f67])).
% 1.57/0.59  fof(f67,plain,(
% 1.57/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.57/0.59    inference(definition_unfolding,[],[f46,f45])).
% 1.57/0.59  fof(f45,plain,(
% 1.57/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f12])).
% 1.57/0.59  fof(f12,axiom,(
% 1.57/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.57/0.59  fof(f46,plain,(
% 1.57/0.59    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f6])).
% 1.57/0.59  fof(f6,axiom,(
% 1.57/0.59    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.57/0.59  fof(f320,plain,(
% 1.57/0.59    ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    inference(resolution,[],[f318,f72])).
% 1.57/0.59  fof(f72,plain,(
% 1.57/0.59    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f71])).
% 1.57/0.59  fof(f71,plain,(
% 1.57/0.59    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(equality_resolution,[],[f65])).
% 1.57/0.59  fof(f65,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f39])).
% 1.57/0.59  fof(f39,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(nnf_transformation,[],[f33])).
% 1.57/0.59  fof(f33,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(flattening,[],[f32])).
% 1.57/0.59  fof(f32,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.59    inference(ennf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.57/0.59  fof(f318,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.59    inference(forward_demodulation,[],[f317,f125])).
% 1.57/0.59  fof(f125,plain,(
% 1.57/0.59    sK0 = k2_relat_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f124,f50])).
% 1.57/0.59  fof(f124,plain,(
% 1.57/0.59    sK0 = k2_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.57/0.59    inference(resolution,[],[f105,f43])).
% 1.57/0.59  fof(f105,plain,(
% 1.57/0.59    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK0 = k2_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(resolution,[],[f83,f43])).
% 1.57/0.59  fof(f83,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | sK0 = k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 1.57/0.59    inference(resolution,[],[f80,f47])).
% 1.57/0.59  fof(f80,plain,(
% 1.57/0.59    ( ! [X0] : (~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 1.57/0.59    inference(resolution,[],[f79,f60])).
% 1.57/0.59  fof(f60,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(ennf_transformation,[],[f4])).
% 1.57/0.59  fof(f4,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.57/0.59  fof(f79,plain,(
% 1.57/0.59    ~v5_relat_1(sK1,sK0) | sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.59    inference(resolution,[],[f77,f51])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f38])).
% 1.57/0.59  fof(f38,plain,(
% 1.57/0.59    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.59    inference(nnf_transformation,[],[f22])).
% 1.57/0.59  fof(f22,plain,(
% 1.57/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.59    inference(flattening,[],[f21])).
% 1.57/0.59  fof(f21,plain,(
% 1.57/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f8])).
% 1.57/0.59  fof(f8,axiom,(
% 1.57/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.57/0.59  fof(f77,plain,(
% 1.57/0.59    v2_funct_2(sK1,sK0)),
% 1.57/0.59    inference(subsumption_resolution,[],[f76,f42])).
% 1.57/0.59  fof(f76,plain,(
% 1.57/0.59    v2_funct_2(sK1,sK0) | ~v3_funct_2(sK1,sK0,sK0)),
% 1.57/0.59    inference(resolution,[],[f75,f43])).
% 1.57/0.59  fof(f75,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_2(sK1,X1) | ~v3_funct_2(sK1,X0,X1)) )),
% 1.57/0.59    inference(resolution,[],[f63,f40])).
% 1.57/0.59  fof(f63,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f31])).
% 1.57/0.59  fof(f317,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f316,f40])).
% 1.57/0.59  fof(f316,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.57/0.59    inference(superposition,[],[f315,f68])).
% 1.57/0.59  fof(f68,plain,(
% 1.57/0.59    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f49,f45])).
% 1.57/0.59  fof(f49,plain,(
% 1.57/0.59    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f20])).
% 1.57/0.59  fof(f20,plain,(
% 1.57/0.59    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f19])).
% 1.57/0.59  fof(f19,plain,(
% 1.57/0.59    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.57/0.59  fof(f315,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.57/0.59    inference(subsumption_resolution,[],[f314,f94])).
% 1.57/0.59  fof(f94,plain,(
% 1.57/0.59    v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.59    inference(subsumption_resolution,[],[f93,f40])).
% 1.57/0.59  fof(f93,plain,(
% 1.57/0.59    v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f92,f41])).
% 1.57/0.59  fof(f41,plain,(
% 1.57/0.59    v1_funct_2(sK1,sK0,sK0)),
% 1.57/0.59    inference(cnf_transformation,[],[f37])).
% 1.57/0.59  fof(f92,plain,(
% 1.57/0.59    v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f91,f42])).
% 1.57/0.59  fof(f91,plain,(
% 1.57/0.59    v1_funct_1(k2_funct_1(sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f90,f43])).
% 1.57/0.59  fof(f90,plain,(
% 1.57/0.59    v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(superposition,[],[f54,f87])).
% 1.57/0.59  fof(f87,plain,(
% 1.57/0.59    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f86,f40])).
% 1.57/0.59  fof(f86,plain,(
% 1.57/0.59    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f85,f42])).
% 1.57/0.59  fof(f85,plain,(
% 1.57/0.59    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f84,f43])).
% 1.57/0.59  fof(f84,plain,(
% 1.57/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(resolution,[],[f53,f41])).
% 1.57/0.59  fof(f53,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f24])).
% 1.57/0.59  fof(f24,plain,(
% 1.57/0.59    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.57/0.59    inference(flattening,[],[f23])).
% 1.57/0.59  fof(f23,plain,(
% 1.57/0.59    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f11])).
% 1.57/0.59  fof(f11,axiom,(
% 1.57/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.57/0.59  fof(f54,plain,(
% 1.57/0.59    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f26])).
% 1.57/0.59  fof(f26,plain,(
% 1.57/0.59    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.57/0.59    inference(flattening,[],[f25])).
% 1.57/0.59  fof(f25,plain,(
% 1.57/0.59    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f9])).
% 1.57/0.59  fof(f9,axiom,(
% 1.57/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.57/0.59  fof(f314,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.59    inference(subsumption_resolution,[],[f313,f115])).
% 1.57/0.59  fof(f115,plain,(
% 1.57/0.59    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    inference(subsumption_resolution,[],[f114,f40])).
% 1.57/0.59  fof(f114,plain,(
% 1.57/0.59    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f113,f41])).
% 1.57/0.59  fof(f113,plain,(
% 1.57/0.59    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f112,f42])).
% 1.57/0.59  fof(f112,plain,(
% 1.57/0.59    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f111,f43])).
% 1.57/0.59  fof(f111,plain,(
% 1.57/0.59    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(superposition,[],[f57,f87])).
% 1.57/0.59  fof(f57,plain,(
% 1.57/0.59    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f26])).
% 1.57/0.59  fof(f313,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.59    inference(subsumption_resolution,[],[f312,f40])).
% 1.57/0.59  fof(f312,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.59    inference(subsumption_resolution,[],[f311,f43])).
% 1.57/0.59  fof(f311,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.59    inference(superposition,[],[f302,f66])).
% 1.57/0.59  fof(f66,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f35])).
% 1.57/0.59  fof(f35,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.57/0.59    inference(flattening,[],[f34])).
% 1.57/0.59  fof(f34,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.57/0.59    inference(ennf_transformation,[],[f10])).
% 1.57/0.59  fof(f10,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.57/0.59  fof(f302,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.57/0.59    inference(subsumption_resolution,[],[f301,f67])).
% 1.57/0.59  fof(f301,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    inference(resolution,[],[f300,f72])).
% 1.57/0.59  fof(f300,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.57/0.59    inference(backward_demodulation,[],[f123,f298])).
% 1.57/0.59  fof(f298,plain,(
% 1.57/0.59    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 1.57/0.59    inference(subsumption_resolution,[],[f297,f110])).
% 1.57/0.59  fof(f110,plain,(
% 1.57/0.59    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.57/0.59    inference(subsumption_resolution,[],[f109,f40])).
% 1.57/0.59  fof(f109,plain,(
% 1.57/0.59    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f108,f41])).
% 1.57/0.59  fof(f108,plain,(
% 1.57/0.59    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.59    inference(subsumption_resolution,[],[f107,f42])).
% 1.57/0.60  % (23448)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.60  % (23439)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.60  % (23435)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.57/0.60  % (23438)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.57/0.61  % (23423)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.57/0.61  fof(f107,plain,(
% 1.57/0.61    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f106,f43])).
% 1.57/0.61  fof(f106,plain,(
% 1.57/0.61    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(superposition,[],[f56,f87])).
% 1.57/0.61  fof(f56,plain,(
% 1.57/0.61    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f26])).
% 1.57/0.61  fof(f297,plain,(
% 1.57/0.61    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 1.57/0.61    inference(resolution,[],[f289,f115])).
% 1.57/0.61  fof(f289,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(k2_funct_1(sK1),X0,X1) | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))) )),
% 1.57/0.61    inference(subsumption_resolution,[],[f288,f50])).
% 1.57/0.61  fof(f288,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v3_funct_2(k2_funct_1(sK1),X0,X1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))) )),
% 1.57/0.61    inference(resolution,[],[f285,f115])).
% 1.57/0.61  fof(f285,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(X2)) | ~v3_funct_2(k2_funct_1(sK1),X0,X1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_relat_1(X2)) )),
% 1.57/0.61    inference(resolution,[],[f280,f47])).
% 1.57/0.61  fof(f280,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(k2_funct_1(sK1)) | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v3_funct_2(k2_funct_1(sK1),X0,X1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.61    inference(backward_demodulation,[],[f273,f276])).
% 1.57/0.61  fof(f276,plain,(
% 1.57/0.61    sK0 = k2_relat_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f275,f50])).
% 1.57/0.61  fof(f275,plain,(
% 1.57/0.61    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.57/0.61    inference(resolution,[],[f274,f115])).
% 1.57/0.61  fof(f274,plain,(
% 1.57/0.61    ( ! [X0] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(X0)) | sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(X0)) )),
% 1.57/0.61    inference(resolution,[],[f135,f115])).
% 1.57/0.61  fof(f135,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | sK0 = k2_relat_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 1.57/0.61    inference(resolution,[],[f129,f47])).
% 1.57/0.61  fof(f129,plain,(
% 1.57/0.61    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK1)) | sK0 = k2_relat_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 1.57/0.61    inference(resolution,[],[f118,f60])).
% 1.57/0.61  fof(f118,plain,(
% 1.57/0.61    ~v5_relat_1(k2_funct_1(sK1),sK0) | sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(resolution,[],[f117,f51])).
% 1.57/0.61  fof(f117,plain,(
% 1.57/0.61    v2_funct_2(k2_funct_1(sK1),sK0)),
% 1.57/0.61    inference(subsumption_resolution,[],[f116,f110])).
% 1.57/0.61  fof(f116,plain,(
% 1.57/0.61    v2_funct_2(k2_funct_1(sK1),sK0) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.57/0.61    inference(resolution,[],[f115,f95])).
% 1.57/0.61  fof(f95,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_2(k2_funct_1(sK1),X1) | ~v3_funct_2(k2_funct_1(sK1),X0,X1)) )),
% 1.57/0.61    inference(resolution,[],[f94,f63])).
% 1.57/0.61  fof(f273,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v3_funct_2(k2_funct_1(sK1),X0,X1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.61    inference(subsumption_resolution,[],[f272,f94])).
% 1.57/0.61  fof(f272,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v3_funct_2(k2_funct_1(sK1),X0,X1) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.61    inference(resolution,[],[f261,f62])).
% 1.57/0.61  fof(f261,plain,(
% 1.57/0.61    ~v2_funct_1(k2_funct_1(sK1)) | k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f257,f94])).
% 1.57/0.61  fof(f257,plain,(
% 1.57/0.61    k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(superposition,[],[f68,f224])).
% 1.57/0.61  fof(f224,plain,(
% 1.57/0.61    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f223,f50])).
% 1.57/0.61  fof(f223,plain,(
% 1.57/0.61    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.57/0.61    inference(resolution,[],[f222,f43])).
% 1.57/0.61  fof(f222,plain,(
% 1.57/0.61    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(X0)) )),
% 1.57/0.61    inference(resolution,[],[f221,f47])).
% 1.57/0.61  fof(f221,plain,(
% 1.57/0.61    ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f220,f67])).
% 1.57/0.61  fof(f220,plain,(
% 1.57/0.61    ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.61    inference(resolution,[],[f215,f72])).
% 1.57/0.61  fof(f215,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f214,f43])).
% 1.57/0.61  fof(f214,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.61    inference(subsumption_resolution,[],[f213,f179])).
% 1.57/0.61  fof(f179,plain,(
% 1.57/0.61    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.61    inference(subsumption_resolution,[],[f178,f94])).
% 1.57/0.61  fof(f178,plain,(
% 1.57/0.61    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f177,f100])).
% 1.57/0.61  fof(f100,plain,(
% 1.57/0.61    v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 1.57/0.61    inference(forward_demodulation,[],[f99,f87])).
% 1.57/0.61  fof(f99,plain,(
% 1.57/0.61    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)),
% 1.57/0.61    inference(subsumption_resolution,[],[f98,f40])).
% 1.57/0.61  fof(f98,plain,(
% 1.57/0.61    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f97,f42])).
% 1.57/0.61  fof(f97,plain,(
% 1.57/0.61    ~v3_funct_2(sK1,sK0,sK0) | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f96,f43])).
% 1.57/0.61  fof(f96,plain,(
% 1.57/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(resolution,[],[f55,f41])).
% 1.57/0.61  fof(f55,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f26])).
% 1.57/0.61  fof(f177,plain,(
% 1.57/0.61    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f176,f110])).
% 1.57/0.61  fof(f176,plain,(
% 1.57/0.61    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f169,f115])).
% 1.57/0.61  fof(f169,plain,(
% 1.57/0.61    m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(superposition,[],[f57,f153])).
% 1.57/0.61  fof(f153,plain,(
% 1.57/0.61    k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f152,f115])).
% 1.57/0.61  fof(f152,plain,(
% 1.57/0.61    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1))),
% 1.57/0.61    inference(resolution,[],[f104,f110])).
% 1.57/0.61  fof(f104,plain,(
% 1.57/0.61    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1))),
% 1.57/0.61    inference(subsumption_resolution,[],[f102,f94])).
% 1.57/0.61  fof(f102,plain,(
% 1.57/0.61    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | k2_funct_1(k2_funct_1(sK1)) = k2_funct_2(sK0,k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.57/0.61    inference(resolution,[],[f100,f53])).
% 1.57/0.61  fof(f213,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.61    inference(resolution,[],[f202,f64])).
% 1.57/0.61  fof(f64,plain,(
% 1.57/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f39])).
% 1.57/0.61  fof(f202,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_1(k2_funct_1(sK1))) | ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(forward_demodulation,[],[f201,f125])).
% 1.57/0.61  fof(f201,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_1(k2_funct_1(sK1))) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(forward_demodulation,[],[f200,f153])).
% 1.57/0.61  fof(f200,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f199,f94])).
% 1.57/0.61  fof(f199,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f198,f100])).
% 1.57/0.61  fof(f198,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f197,f110])).
% 1.57/0.61  fof(f197,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f196,f40])).
% 1.57/0.61  fof(f196,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f195,f41])).
% 1.57/0.61  fof(f195,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f194,f42])).
% 1.57/0.61  fof(f194,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f193,f43])).
% 1.57/0.61  fof(f193,plain,(
% 1.57/0.61    r2_relset_1(sK0,sK0,sK1,k2_funct_2(sK0,k2_funct_1(sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.57/0.61    inference(resolution,[],[f148,f115])).
% 1.57/0.61  fof(f148,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | r2_relset_1(X1,X1,X0,k2_funct_2(X1,k2_funct_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(X0,X1,X1) | ~v1_funct_2(X0,X1,X1) | ~v1_funct_1(X0) | ~r2_relset_1(X1,X1,k6_partfun1(k2_relat_1(X0)),k6_partfun1(X1)) | ~v3_funct_2(k2_funct_1(X0),X1,X1) | ~v1_funct_2(k2_funct_1(X0),X1,X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.57/0.61    inference(subsumption_resolution,[],[f147,f62])).
% 1.57/0.61  fof(f147,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r2_relset_1(X1,X1,k6_partfun1(k2_relat_1(X0)),k6_partfun1(X1)) | r2_relset_1(X1,X1,X0,k2_funct_2(X1,k2_funct_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(X0,X1,X1) | ~v1_funct_2(X0,X1,X1) | ~v1_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(k2_funct_1(X0),X1,X1) | ~v1_funct_2(k2_funct_1(X0),X1,X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.61    inference(duplicate_literal_removal,[],[f144])).
% 1.57/0.61  fof(f144,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r2_relset_1(X1,X1,k6_partfun1(k2_relat_1(X0)),k6_partfun1(X1)) | r2_relset_1(X1,X1,X0,k2_funct_2(X1,k2_funct_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(X0,X1,X1) | ~v1_funct_2(X0,X1,X1) | ~v1_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v3_funct_2(k2_funct_1(X0),X1,X1) | ~v1_funct_2(k2_funct_1(X0),X1,X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.61    inference(superposition,[],[f127,f68])).
% 1.57/0.61  fof(f127,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (~r2_relset_1(X0,X0,k5_relat_1(X1,X2),k6_partfun1(X0)) | r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X2,X0,X0) | ~v1_funct_2(X2,X0,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.61    inference(duplicate_literal_removal,[],[f126])).
% 1.57/0.61  fof(f126,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (~r2_relset_1(X0,X0,k5_relat_1(X1,X2),k6_partfun1(X0)) | r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X2,X0,X0) | ~v1_funct_2(X2,X0,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 1.57/0.61    inference(superposition,[],[f58,f66])).
% 1.57/0.61  fof(f58,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) | r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X2,X0,X0) | ~v1_funct_2(X2,X0,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f28])).
% 1.57/0.61  fof(f28,plain,(
% 1.57/0.61    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X2,X0,X0) | ~v1_funct_2(X2,X0,X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.57/0.61    inference(flattening,[],[f27])).
% 1.57/0.61  fof(f27,plain,(
% 1.57/0.61    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X2,X0,X0) | ~v1_funct_2(X2,X0,X0) | ~v1_funct_1(X2))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.57/0.61    inference(ennf_transformation,[],[f13])).
% 1.57/0.61  fof(f13,axiom,(
% 1.57/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 1.57/0.61  fof(f123,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 1.57/0.61    inference(subsumption_resolution,[],[f122,f40])).
% 1.57/0.61  fof(f122,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f121,f43])).
% 1.57/0.61  fof(f121,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f120,f94])).
% 1.57/0.61  fof(f120,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(subsumption_resolution,[],[f119,f115])).
% 1.57/0.61  fof(f119,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.57/0.61    inference(superposition,[],[f89,f66])).
% 1.57/0.61  fof(f89,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.57/0.61    inference(forward_demodulation,[],[f88,f87])).
% 1.57/0.61  fof(f88,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 1.57/0.61    inference(backward_demodulation,[],[f44,f87])).
% 1.57/0.61  fof(f44,plain,(
% 1.57/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 1.57/0.61    inference(cnf_transformation,[],[f37])).
% 1.57/0.61  fof(f42,plain,(
% 1.57/0.61    v3_funct_2(sK1,sK0,sK0)),
% 1.57/0.61    inference(cnf_transformation,[],[f37])).
% 1.57/0.61  fof(f43,plain,(
% 1.57/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.61    inference(cnf_transformation,[],[f37])).
% 1.57/0.61  fof(f50,plain,(
% 1.57/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f2])).
% 1.57/0.61  fof(f2,axiom,(
% 1.57/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.57/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.57/0.61  % SZS output end Proof for theBenchmark
% 1.57/0.61  % (23447)------------------------------
% 1.57/0.61  % (23447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (23447)Termination reason: Refutation
% 1.57/0.61  
% 1.57/0.61  % (23447)Memory used [KB]: 6524
% 1.57/0.61  % (23447)Time elapsed: 0.182 s
% 1.57/0.61  % (23447)------------------------------
% 1.57/0.61  % (23447)------------------------------
% 1.57/0.62  % (23417)Success in time 0.258 s
%------------------------------------------------------------------------------
