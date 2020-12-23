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
% DateTime   : Thu Dec  3 13:05:23 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 960 expanded)
%              Number of leaves         :   14 ( 271 expanded)
%              Depth                    :   21
%              Number of atoms          :  354 (6362 expanded)
%              Number of equality atoms :   91 ( 982 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(subsumption_resolution,[],[f344,f74])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f65,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & sK0 = k2_relset_1(sK0,sK0,sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & k2_relset_1(X0,X0,X1) = X0
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & sK0 = k2_relset_1(sK0,sK0,sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
        & sK0 = k2_relset_1(sK0,sK0,sK1)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
      & sK0 = k2_relset_1(sK0,sK0,sK1)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f344,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f66,f343])).

fof(f343,plain,(
    sK2 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f331,f316])).

fof(f316,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f315,f105])).

fof(f105,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f104,f68])).

fof(f68,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f104,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f72,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f315,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f274,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f274,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f260])).

fof(f260,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f114,f246])).

fof(f246,plain,(
    sK1 = k5_relat_1(sK1,sK2) ),
    inference(resolution,[],[f163,f150])).

fof(f150,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k5_relat_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f148,f146])).

fof(f146,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f144,f39])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f144,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f97,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f95,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f59,f42])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f148,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f84,f146])).

fof(f84,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f163,plain,(
    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f162,f146])).

fof(f162,plain,(
    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f160,f39])).

% (4729)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f160,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f101,f40])).

fof(f101,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f61,f42])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f114,plain,
    ( k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,sK2))
    | r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f112,f68])).

fof(f112,plain,
    ( k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,sK2))
    | r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f81,f41])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,X0))
      | r1_tarski(sK0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f80,f77])).

fof(f77,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f75,f44])).

fof(f44,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f55,f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f80,plain,(
    ! [X0] :
      ( k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,X0))
      | r1_tarski(k2_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f78,f67])).

fof(f67,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f54,f40])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,X0))
      | r1_tarski(k2_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f331,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f273,f316])).

fof(f273,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( sK1 != sK1
    | sK0 != k1_relat_1(sK2)
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f135,f246])).

fof(f135,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | sK1 != k5_relat_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f134,f77])).

fof(f134,plain,
    ( k2_relat_1(sK1) != k1_relat_1(sK2)
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | sK1 != k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f132,f67])).

fof(f132,plain,
    ( k2_relat_1(sK1) != k1_relat_1(sK2)
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | sK1 != k5_relat_1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f89,f39])).

fof(f89,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(sK2)
      | sK2 = k6_relat_1(k1_relat_1(sK2))
      | k5_relat_1(X1,sK2) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f87,f68])).

fof(f87,plain,(
    ! [X1] :
      ( k5_relat_1(X1,sK2) != X1
      | k2_relat_1(X1) != k1_relat_1(sK2)
      | sK2 = k6_relat_1(k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k1_relat_1(X1) != k2_relat_1(X0)
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k1_relat_1(X1) = k2_relat_1(X0) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f66,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f45,f46])).

fof(f46,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f45,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (4712)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (4713)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (4720)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (4724)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (4727)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (4719)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.55  % (4719)Refutation found. Thanks to Tanya!
% 1.28/0.55  % SZS status Theorem for theBenchmark
% 1.28/0.55  % (4736)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.28/0.55  % (4725)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.28/0.55  % SZS output start Proof for theBenchmark
% 1.28/0.55  fof(f345,plain,(
% 1.28/0.55    $false),
% 1.28/0.55    inference(subsumption_resolution,[],[f344,f74])).
% 1.28/0.55  fof(f74,plain,(
% 1.28/0.55    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.28/0.55    inference(resolution,[],[f65,f42])).
% 1.28/0.55  fof(f42,plain,(
% 1.28/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.55    inference(cnf_transformation,[],[f34])).
% 1.28/0.55  fof(f34,plain,(
% 1.28/0.55    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 1.28/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32])).
% 1.28/0.55  fof(f32,plain,(
% 1.28/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 1.28/0.55    introduced(choice_axiom,[])).
% 1.28/0.55  fof(f33,plain,(
% 1.28/0.55    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & sK0 = k2_relset_1(sK0,sK0,sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2))),
% 1.28/0.55    introduced(choice_axiom,[])).
% 1.28/0.55  fof(f17,plain,(
% 1.28/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.28/0.55    inference(flattening,[],[f16])).
% 1.28/0.55  fof(f16,plain,(
% 1.28/0.55    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.28/0.55    inference(ennf_transformation,[],[f14])).
% 1.28/0.55  fof(f14,plain,(
% 1.28/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.28/0.55    inference(pure_predicate_removal,[],[f13])).
% 1.28/0.55  fof(f13,negated_conjecture,(
% 1.28/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.28/0.55    inference(negated_conjecture,[],[f12])).
% 1.28/0.55  fof(f12,conjecture,(
% 1.28/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).
% 1.28/0.55  fof(f65,plain,(
% 1.28/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.28/0.55    inference(duplicate_literal_removal,[],[f64])).
% 1.28/0.55  fof(f64,plain,(
% 1.28/0.55    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.55    inference(equality_resolution,[],[f58])).
% 1.28/0.55  fof(f58,plain,(
% 1.28/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.55    inference(cnf_transformation,[],[f38])).
% 1.28/0.55  fof(f38,plain,(
% 1.28/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(nnf_transformation,[],[f27])).
% 1.28/0.55  fof(f27,plain,(
% 1.28/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(flattening,[],[f26])).
% 1.28/0.55  fof(f26,plain,(
% 1.28/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.28/0.55    inference(ennf_transformation,[],[f8])).
% 1.28/0.55  fof(f8,axiom,(
% 1.28/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.28/0.55  fof(f344,plain,(
% 1.28/0.55    ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.28/0.55    inference(backward_demodulation,[],[f66,f343])).
% 1.28/0.55  fof(f343,plain,(
% 1.28/0.55    sK2 = k6_relat_1(sK0)),
% 1.28/0.55    inference(subsumption_resolution,[],[f331,f316])).
% 1.28/0.55  fof(f316,plain,(
% 1.28/0.55    sK0 = k1_relat_1(sK2)),
% 1.28/0.55    inference(subsumption_resolution,[],[f315,f105])).
% 1.28/0.55  fof(f105,plain,(
% 1.28/0.55    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.28/0.55    inference(subsumption_resolution,[],[f104,f68])).
% 1.28/0.55  fof(f68,plain,(
% 1.28/0.55    v1_relat_1(sK2)),
% 1.28/0.55    inference(resolution,[],[f54,f42])).
% 1.28/0.55  fof(f54,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f23])).
% 1.28/0.55  fof(f23,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(ennf_transformation,[],[f5])).
% 1.28/0.55  fof(f5,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.28/0.55  fof(f104,plain,(
% 1.28/0.55    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.28/0.55    inference(resolution,[],[f72,f49])).
% 1.28/0.55  fof(f49,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f35])).
% 1.28/0.55  fof(f35,plain,(
% 1.28/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.28/0.55    inference(nnf_transformation,[],[f22])).
% 1.28/0.55  fof(f22,plain,(
% 1.28/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.28/0.55    inference(ennf_transformation,[],[f2])).
% 1.28/0.55  fof(f2,axiom,(
% 1.28/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.28/0.55  fof(f72,plain,(
% 1.28/0.55    v4_relat_1(sK2,sK0)),
% 1.28/0.55    inference(resolution,[],[f56,f42])).
% 1.28/0.55  fof(f56,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f25])).
% 1.28/0.55  fof(f25,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(ennf_transformation,[],[f15])).
% 1.28/0.55  fof(f15,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.28/0.55    inference(pure_predicate_removal,[],[f6])).
% 1.28/0.55  fof(f6,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.28/0.55  fof(f315,plain,(
% 1.28/0.55    sK0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0)),
% 1.28/0.55    inference(resolution,[],[f274,f53])).
% 1.28/0.55  fof(f53,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f37])).
% 1.28/0.55  fof(f37,plain,(
% 1.28/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.55    inference(flattening,[],[f36])).
% 1.28/0.55  fof(f36,plain,(
% 1.28/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.55    inference(nnf_transformation,[],[f1])).
% 1.28/0.55  fof(f1,axiom,(
% 1.28/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.55  fof(f274,plain,(
% 1.28/0.55    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.28/0.55    inference(trivial_inequality_removal,[],[f260])).
% 1.28/0.55  fof(f260,plain,(
% 1.28/0.55    k1_relat_1(sK1) != k1_relat_1(sK1) | r1_tarski(sK0,k1_relat_1(sK2))),
% 1.28/0.55    inference(backward_demodulation,[],[f114,f246])).
% 1.28/0.55  fof(f246,plain,(
% 1.28/0.55    sK1 = k5_relat_1(sK1,sK2)),
% 1.28/0.55    inference(resolution,[],[f163,f150])).
% 1.28/0.55  fof(f150,plain,(
% 1.28/0.55    ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k5_relat_1(sK1,sK2)),
% 1.28/0.55    inference(forward_demodulation,[],[f148,f146])).
% 1.28/0.55  fof(f146,plain,(
% 1.28/0.55    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)),
% 1.28/0.55    inference(subsumption_resolution,[],[f144,f39])).
% 1.28/0.55  fof(f39,plain,(
% 1.28/0.55    v1_funct_1(sK1)),
% 1.28/0.55    inference(cnf_transformation,[],[f34])).
% 1.28/0.55  fof(f144,plain,(
% 1.28/0.55    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) | ~v1_funct_1(sK1)),
% 1.28/0.55    inference(resolution,[],[f97,f40])).
% 1.28/0.55  fof(f40,plain,(
% 1.28/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.55    inference(cnf_transformation,[],[f34])).
% 1.28/0.55  fof(f97,plain,(
% 1.28/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2) | ~v1_funct_1(X5)) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f95,f41])).
% 1.28/0.55  fof(f41,plain,(
% 1.28/0.55    v1_funct_1(sK2)),
% 1.28/0.55    inference(cnf_transformation,[],[f34])).
% 1.28/0.55  fof(f95,plain,(
% 1.28/0.55    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK0,sK0,X5,sK2) = k5_relat_1(X5,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.28/0.55    inference(resolution,[],[f59,f42])).
% 1.28/0.55  fof(f59,plain,(
% 1.28/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f29])).
% 1.28/0.55  fof(f29,plain,(
% 1.28/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.28/0.55    inference(flattening,[],[f28])).
% 1.28/0.55  fof(f28,plain,(
% 1.28/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.28/0.55    inference(ennf_transformation,[],[f10])).
% 1.28/0.55  fof(f10,axiom,(
% 1.28/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.28/0.55  fof(f148,plain,(
% 1.28/0.55    ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 1.28/0.55    inference(backward_demodulation,[],[f84,f146])).
% 1.28/0.55  fof(f84,plain,(
% 1.28/0.55    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.55    inference(subsumption_resolution,[],[f83,f40])).
% 1.28/0.55  fof(f83,plain,(
% 1.28/0.55    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.55    inference(resolution,[],[f57,f43])).
% 1.28/0.55  fof(f43,plain,(
% 1.28/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 1.28/0.55    inference(cnf_transformation,[],[f34])).
% 1.28/0.55  fof(f57,plain,(
% 1.28/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.55    inference(cnf_transformation,[],[f38])).
% 1.28/0.55  fof(f163,plain,(
% 1.28/0.55    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.55    inference(forward_demodulation,[],[f162,f146])).
% 1.28/0.55  fof(f162,plain,(
% 1.28/0.55    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.55    inference(subsumption_resolution,[],[f160,f39])).
% 1.28/0.55  % (4729)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.55  fof(f160,plain,(
% 1.28/0.55    m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 1.28/0.55    inference(resolution,[],[f101,f40])).
% 1.28/0.55  fof(f101,plain,(
% 1.28/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(X5)) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f99,f41])).
% 1.28/0.55  fof(f99,plain,(
% 1.28/0.55    ( ! [X4,X5,X3] : (m1_subset_1(k1_partfun1(X3,X4,sK0,sK0,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.28/0.55    inference(resolution,[],[f61,f42])).
% 1.28/0.55  fof(f61,plain,(
% 1.28/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f31])).
% 1.28/0.55  fof(f31,plain,(
% 1.28/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.28/0.55    inference(flattening,[],[f30])).
% 1.28/0.55  fof(f30,plain,(
% 1.28/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.28/0.55    inference(ennf_transformation,[],[f9])).
% 1.28/0.55  fof(f9,axiom,(
% 1.28/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.28/0.55  fof(f114,plain,(
% 1.28/0.55    k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,sK2)) | r1_tarski(sK0,k1_relat_1(sK2))),
% 1.28/0.55    inference(subsumption_resolution,[],[f112,f68])).
% 1.28/0.55  fof(f112,plain,(
% 1.28/0.55    k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,sK2)) | r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.28/0.55    inference(resolution,[],[f81,f41])).
% 1.28/0.55  fof(f81,plain,(
% 1.28/0.55    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,X0)) | r1_tarski(sK0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.28/0.55    inference(forward_demodulation,[],[f80,f77])).
% 1.28/0.55  fof(f77,plain,(
% 1.28/0.55    sK0 = k2_relat_1(sK1)),
% 1.28/0.55    inference(forward_demodulation,[],[f75,f44])).
% 1.28/0.55  fof(f44,plain,(
% 1.28/0.55    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.28/0.55    inference(cnf_transformation,[],[f34])).
% 1.28/0.55  fof(f75,plain,(
% 1.28/0.55    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.28/0.55    inference(resolution,[],[f55,f40])).
% 1.28/0.55  fof(f55,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f24])).
% 1.28/0.55  fof(f24,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(ennf_transformation,[],[f7])).
% 1.28/0.55  fof(f7,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.28/0.55  fof(f80,plain,(
% 1.28/0.55    ( ! [X0] : (k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,X0)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f78,f67])).
% 1.28/0.55  fof(f67,plain,(
% 1.28/0.55    v1_relat_1(sK1)),
% 1.28/0.55    inference(resolution,[],[f54,f40])).
% 1.28/0.55  fof(f78,plain,(
% 1.28/0.55    ( ! [X0] : (k1_relat_1(sK1) != k1_relat_1(k5_relat_1(sK1,X0)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(X0)) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.55    inference(resolution,[],[f47,f39])).
% 1.28/0.55  fof(f47,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f19])).
% 1.28/0.55  fof(f19,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.55    inference(flattening,[],[f18])).
% 1.28/0.55  fof(f18,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.55    inference(ennf_transformation,[],[f3])).
% 1.28/0.55  fof(f3,axiom,(
% 1.28/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.28/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 1.28/0.56  fof(f331,plain,(
% 1.28/0.56    sK2 = k6_relat_1(sK0) | sK0 != k1_relat_1(sK2)),
% 1.28/0.56    inference(backward_demodulation,[],[f273,f316])).
% 1.28/0.56  fof(f273,plain,(
% 1.28/0.56    sK0 != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 1.28/0.56    inference(trivial_inequality_removal,[],[f261])).
% 1.28/0.56  fof(f261,plain,(
% 1.28/0.56    sK1 != sK1 | sK0 != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 1.28/0.56    inference(backward_demodulation,[],[f135,f246])).
% 1.28/0.56  fof(f135,plain,(
% 1.28/0.56    sK0 != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2)) | sK1 != k5_relat_1(sK1,sK2)),
% 1.28/0.56    inference(forward_demodulation,[],[f134,f77])).
% 1.28/0.56  fof(f134,plain,(
% 1.28/0.56    k2_relat_1(sK1) != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2)) | sK1 != k5_relat_1(sK1,sK2)),
% 1.28/0.56    inference(subsumption_resolution,[],[f132,f67])).
% 1.28/0.56  fof(f132,plain,(
% 1.28/0.56    k2_relat_1(sK1) != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2)) | sK1 != k5_relat_1(sK1,sK2) | ~v1_relat_1(sK1)),
% 1.28/0.56    inference(resolution,[],[f89,f39])).
% 1.28/0.56  fof(f89,plain,(
% 1.28/0.56    ( ! [X1] : (~v1_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2)) | k5_relat_1(X1,sK2) != X1 | ~v1_relat_1(X1)) )),
% 1.28/0.56    inference(subsumption_resolution,[],[f87,f68])).
% 1.28/0.56  fof(f87,plain,(
% 1.28/0.56    ( ! [X1] : (k5_relat_1(X1,sK2) != X1 | k2_relat_1(X1) != k1_relat_1(sK2) | sK2 = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.28/0.56    inference(resolution,[],[f48,f41])).
% 1.28/0.56  fof(f48,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f21])).
% 1.28/0.56  fof(f21,plain,(
% 1.28/0.56    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.56    inference(flattening,[],[f20])).
% 1.28/0.56  fof(f20,plain,(
% 1.28/0.56    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.56    inference(ennf_transformation,[],[f4])).
% 1.28/0.56  fof(f4,axiom,(
% 1.28/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 1.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 1.28/0.56  fof(f66,plain,(
% 1.28/0.56    ~r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.28/0.56    inference(forward_demodulation,[],[f45,f46])).
% 1.28/0.56  fof(f46,plain,(
% 1.28/0.56    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f11])).
% 1.28/0.56  fof(f11,axiom,(
% 1.28/0.56    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.28/0.56  fof(f45,plain,(
% 1.28/0.56    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.28/0.56    inference(cnf_transformation,[],[f34])).
% 1.28/0.56  % SZS output end Proof for theBenchmark
% 1.28/0.56  % (4719)------------------------------
% 1.28/0.56  % (4719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (4719)Termination reason: Refutation
% 1.28/0.56  
% 1.28/0.56  % (4719)Memory used [KB]: 1918
% 1.28/0.56  % (4719)Time elapsed: 0.119 s
% 1.28/0.56  % (4719)------------------------------
% 1.28/0.56  % (4719)------------------------------
% 1.28/0.56  % (4715)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.56  % (4711)Success in time 0.187 s
%------------------------------------------------------------------------------
