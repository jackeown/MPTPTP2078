%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:06 EST 2020

% Result     : Theorem 11.26s
% Output     : CNFRefutation 11.26s
% Verified   : 
% Statistics : Number of formulae       :  250 (1902 expanded)
%              Number of clauses        :  170 ( 607 expanded)
%              Number of leaves         :   21 ( 463 expanded)
%              Depth                    :   18
%              Number of atoms          :  918 (13258 expanded)
%              Number of equality atoms :  410 ( 947 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
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
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f49,f48])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f86,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1016,plain,
    ( X0_50 != X1_50
    | X0_49 != X1_49
    | k2_funct_2(X0_50,X0_49) = k2_funct_2(X1_50,X1_49) ),
    theory(equality)).

cnf(c_2042,plain,
    ( sK0 != X0_50
    | k2_funct_2(sK0,sK1) = k2_funct_2(X0_50,X0_49)
    | sK1 != X0_49 ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_54719,plain,
    ( sK0 != X0_50
    | k2_funct_2(sK0,sK1) = k2_funct_2(X0_50,k2_funct_1(sK2))
    | sK1 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_54720,plain,
    ( sK0 != sK0
    | k2_funct_2(sK0,sK1) = k2_funct_2(sK0,k2_funct_1(sK2))
    | sK1 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_54719])).

cnf(c_1003,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1940,plain,
    ( X0_49 != X1_49
    | X0_49 = k2_funct_2(X0_50,X2_49)
    | k2_funct_2(X0_50,X2_49) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_2116,plain,
    ( X0_49 != k2_funct_2(X0_50,X1_49)
    | X0_49 = k2_funct_2(X1_50,X2_49)
    | k2_funct_2(X1_50,X2_49) != k2_funct_2(X0_50,X1_49) ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_29137,plain,
    ( k2_funct_2(X0_50,X0_49) != k2_funct_2(X1_50,k2_funct_1(sK2))
    | sK2 = k2_funct_2(X0_50,X0_49)
    | sK2 != k2_funct_2(X1_50,k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_29143,plain,
    ( k2_funct_2(sK0,sK1) != k2_funct_2(sK0,k2_funct_1(sK2))
    | sK2 != k2_funct_2(sK0,k2_funct_1(sK2))
    | sK2 = k2_funct_2(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_29137])).

cnf(c_2569,plain,
    ( X0_49 != X1_49
    | X0_49 = k2_funct_1(X2_49)
    | k2_funct_1(X2_49) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_20094,plain,
    ( X0_49 = k2_funct_1(sK2)
    | X0_49 != sK1
    | k2_funct_1(sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_20096,plain,
    ( k2_funct_1(sK2) != sK1
    | sK1 = k2_funct_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_20094])).

cnf(c_2112,plain,
    ( X0_49 = k2_funct_2(X0_50,X1_49)
    | X0_49 != k2_funct_1(X1_49)
    | k2_funct_2(X0_50,X1_49) != k2_funct_1(X1_49) ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_17737,plain,
    ( k2_funct_2(X0_50,k2_funct_1(sK2)) != k2_funct_1(k2_funct_1(sK2))
    | sK2 = k2_funct_2(X0_50,k2_funct_1(sK2))
    | sK2 != k2_funct_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_17738,plain,
    ( k2_funct_2(sK0,k2_funct_1(sK2)) != k2_funct_1(k2_funct_1(sK2))
    | sK2 = k2_funct_2(sK0,k2_funct_1(sK2))
    | sK2 != k2_funct_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_17737])).

cnf(c_1922,plain,
    ( X0_49 != X1_49
    | sK2 != X1_49
    | sK2 = X0_49 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_2001,plain,
    ( X0_49 != sK2
    | sK2 = X0_49
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_8834,plain,
    ( k2_funct_1(k2_funct_1(sK2)) != sK2
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_980,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1551,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_981,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49)
    | k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1550,plain,
    ( k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49)
    | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_2911,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1550])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_41,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3486,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2911,c_39,c_40,c_41])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_987,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1544,plain,
    ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_3867,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3486,c_1544])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8316,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3867,c_39,c_40,c_41,c_42])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_378,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_15])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_390,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_378,c_7])).

cnf(c_466,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_390])).

cnf(c_467,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_970,plain,
    ( ~ v3_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | k2_relat_1(X0_49) = X1_50 ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_1561,plain,
    ( k2_relat_1(X0_49) = X0_50
    | v3_funct_2(X0_49,X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X0_50))) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_8331,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),X0_50,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8316,c_1561])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_990,plain,
    ( ~ v3_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | v2_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1541,plain,
    ( v3_funct_2(X0_49,X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_2422,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1541])).

cnf(c_2673,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2422,c_39,c_41])).

cnf(c_977,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1554,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_996,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1535,plain,
    ( k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49)
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_2219,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1535])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1540,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_1960,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1540])).

cnf(c_2280,plain,
    ( v2_funct_1(sK2) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_1960])).

cnf(c_2281,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2280])).

cnf(c_2678,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2673,c_2281])).

cnf(c_8336,plain,
    ( k1_relat_1(sK2) = sK0
    | v3_funct_2(k2_funct_1(sK2),X0_50,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8331,c_2678])).

cnf(c_8413,plain,
    ( k1_relat_1(sK2) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8336])).

cnf(c_8327,plain,
    ( k2_funct_2(sK0,k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8316,c_1550])).

cnf(c_8324,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8316,c_1540])).

cnf(c_8323,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8316,c_1541])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_993,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1538,plain,
    ( k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49))
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_993])).

cnf(c_2373,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1538])).

cnf(c_2796,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2373,c_39,c_41,c_1960,c_2422])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_992,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(X1_49)
    | k1_relat_1(X0_49) != k2_relat_1(X1_49)
    | k5_relat_1(X1_49,X0_49) != k6_partfun1(k2_relat_1(X0_49))
    | k2_funct_1(X0_49) = X1_49 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1539,plain,
    ( k1_relat_1(X0_49) != k2_relat_1(X1_49)
    | k5_relat_1(X1_49,X0_49) != k6_partfun1(k2_relat_1(X0_49))
    | k2_funct_1(X0_49) = X1_49
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_2886,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_1539])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_995,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1536,plain,
    ( k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49)
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_2291,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1536])).

cnf(c_2577,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2291,c_39,c_41,c_1960,c_2422])).

cnf(c_2895,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2886,c_2577])).

cnf(c_2896,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2895])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_984,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_2(X0_50,X0_49)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1547,plain,
    ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_2(X0_50,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_2454,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1547])).

cnf(c_3338,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2454,c_39,c_40,c_41])).

cnf(c_3489,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3486,c_3338])).

cnf(c_6407,plain,
    ( v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2896,c_39,c_1960,c_3489])).

cnf(c_6408,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6407])).

cnf(c_6411,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6408,c_2678])).

cnf(c_6412,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6411])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_976,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1555,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_982,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1549,plain,
    ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_4021,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK2) = k5_relat_1(X0_49,sK2)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1549])).

cnf(c_4318,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK2) = k5_relat_1(X0_49,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4021,c_39])).

cnf(c_4319,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK2) = k5_relat_1(X0_49,sK2)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4318])).

cnf(c_4328,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_4319])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_434,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_52,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_436,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_52])).

cnf(c_971,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_436])).

cnf(c_1560,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_989,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | m1_subset_1(k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1849,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_2119,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_34,c_31,c_30,c_27,c_971,c_1849])).

cnf(c_4362,plain,
    ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4328,c_2119])).

cnf(c_2260,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_2027,plain,
    ( X0_49 != X1_49
    | X0_49 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_2259,plain,
    ( X0_49 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | X0_49 != k5_relat_1(sK1,sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_2645,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_relat_1(sK1,sK2)
    | k5_relat_1(sK1,sK2) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_1000,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2646,plain,
    ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_1915,plain,
    ( X0_49 != X1_49
    | X0_49 = k6_partfun1(X0_50)
    | k6_partfun1(X0_50) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_2101,plain,
    ( X0_49 != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | X0_49 = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_3508,plain,
    ( k5_relat_1(sK1,sK2) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_relat_1(sK1,sK2) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_6121,plain,
    ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4362,c_34,c_31,c_30,c_27,c_971,c_1849,c_2260,c_2645,c_2646,c_3508])).

cnf(c_6124,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK1)
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = sK1
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6121,c_1539])).

cnf(c_4935,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,X0_50,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1561])).

cnf(c_4997,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4935])).

cnf(c_5316,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4935,c_39,c_41,c_42,c_4997])).

cnf(c_4936,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,X0_50,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1561])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1094,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_5397,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4936,c_34,c_32,c_31,c_1094])).

cnf(c_6125,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = sK1
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6124,c_5316,c_5397])).

cnf(c_6126,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_funct_1(sK2) = sK1
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6125])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_985,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | v1_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1546,plain,
    ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v1_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50) = iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_3034,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1546])).

cnf(c_3627,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3034,c_39,c_40,c_41])).

cnf(c_3631,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3627,c_3486])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_986,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | v3_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1545,plain,
    ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_2996,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1545])).

cnf(c_3559,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2996,c_39,c_40,c_41])).

cnf(c_3563,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3559,c_3486])).

cnf(c_1868,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_funct_2(sK0,sK1) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_424,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k2_funct_2(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_972,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k2_funct_2(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_1065,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_1052,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_1054,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_1001,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1033,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1032,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54720,c_29143,c_20096,c_17738,c_8834,c_8413,c_8327,c_8324,c_8323,c_6412,c_6126,c_3867,c_3631,c_3563,c_3489,c_2422,c_1960,c_1868,c_972,c_1065,c_1054,c_1033,c_1032,c_42,c_41,c_40,c_39,c_38,c_31,c_32,c_33,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 11.26/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.26/2.01  
% 11.26/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.26/2.01  
% 11.26/2.01  ------  iProver source info
% 11.26/2.01  
% 11.26/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.26/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.26/2.01  git: non_committed_changes: false
% 11.26/2.01  git: last_make_outside_of_git: false
% 11.26/2.01  
% 11.26/2.01  ------ 
% 11.26/2.01  
% 11.26/2.01  ------ Input Options
% 11.26/2.01  
% 11.26/2.01  --out_options                           all
% 11.26/2.01  --tptp_safe_out                         true
% 11.26/2.01  --problem_path                          ""
% 11.26/2.01  --include_path                          ""
% 11.26/2.01  --clausifier                            res/vclausify_rel
% 11.26/2.01  --clausifier_options                    --mode clausify
% 11.26/2.01  --stdin                                 false
% 11.26/2.01  --stats_out                             all
% 11.26/2.01  
% 11.26/2.01  ------ General Options
% 11.26/2.01  
% 11.26/2.01  --fof                                   false
% 11.26/2.01  --time_out_real                         305.
% 11.26/2.01  --time_out_virtual                      -1.
% 11.26/2.01  --symbol_type_check                     false
% 11.26/2.01  --clausify_out                          false
% 11.26/2.01  --sig_cnt_out                           false
% 11.26/2.01  --trig_cnt_out                          false
% 11.26/2.01  --trig_cnt_out_tolerance                1.
% 11.26/2.01  --trig_cnt_out_sk_spl                   false
% 11.26/2.01  --abstr_cl_out                          false
% 11.26/2.01  
% 11.26/2.01  ------ Global Options
% 11.26/2.01  
% 11.26/2.01  --schedule                              default
% 11.26/2.01  --add_important_lit                     false
% 11.26/2.01  --prop_solver_per_cl                    1000
% 11.26/2.01  --min_unsat_core                        false
% 11.26/2.01  --soft_assumptions                      false
% 11.26/2.01  --soft_lemma_size                       3
% 11.26/2.01  --prop_impl_unit_size                   0
% 11.26/2.01  --prop_impl_unit                        []
% 11.26/2.01  --share_sel_clauses                     true
% 11.26/2.01  --reset_solvers                         false
% 11.26/2.01  --bc_imp_inh                            [conj_cone]
% 11.26/2.01  --conj_cone_tolerance                   3.
% 11.26/2.01  --extra_neg_conj                        none
% 11.26/2.01  --large_theory_mode                     true
% 11.26/2.01  --prolific_symb_bound                   200
% 11.26/2.01  --lt_threshold                          2000
% 11.26/2.01  --clause_weak_htbl                      true
% 11.26/2.01  --gc_record_bc_elim                     false
% 11.26/2.01  
% 11.26/2.01  ------ Preprocessing Options
% 11.26/2.01  
% 11.26/2.01  --preprocessing_flag                    true
% 11.26/2.01  --time_out_prep_mult                    0.1
% 11.26/2.01  --splitting_mode                        input
% 11.26/2.01  --splitting_grd                         true
% 11.26/2.01  --splitting_cvd                         false
% 11.26/2.01  --splitting_cvd_svl                     false
% 11.26/2.01  --splitting_nvd                         32
% 11.26/2.01  --sub_typing                            true
% 11.26/2.01  --prep_gs_sim                           true
% 11.26/2.01  --prep_unflatten                        true
% 11.26/2.01  --prep_res_sim                          true
% 11.26/2.01  --prep_upred                            true
% 11.26/2.01  --prep_sem_filter                       exhaustive
% 11.26/2.01  --prep_sem_filter_out                   false
% 11.26/2.01  --pred_elim                             true
% 11.26/2.01  --res_sim_input                         true
% 11.26/2.01  --eq_ax_congr_red                       true
% 11.26/2.01  --pure_diseq_elim                       true
% 11.26/2.01  --brand_transform                       false
% 11.26/2.01  --non_eq_to_eq                          false
% 11.26/2.01  --prep_def_merge                        true
% 11.26/2.01  --prep_def_merge_prop_impl              false
% 11.26/2.01  --prep_def_merge_mbd                    true
% 11.26/2.01  --prep_def_merge_tr_red                 false
% 11.26/2.01  --prep_def_merge_tr_cl                  false
% 11.26/2.01  --smt_preprocessing                     true
% 11.26/2.01  --smt_ac_axioms                         fast
% 11.26/2.01  --preprocessed_out                      false
% 11.26/2.01  --preprocessed_stats                    false
% 11.26/2.01  
% 11.26/2.01  ------ Abstraction refinement Options
% 11.26/2.01  
% 11.26/2.01  --abstr_ref                             []
% 11.26/2.01  --abstr_ref_prep                        false
% 11.26/2.01  --abstr_ref_until_sat                   false
% 11.26/2.01  --abstr_ref_sig_restrict                funpre
% 11.26/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.26/2.01  --abstr_ref_under                       []
% 11.26/2.01  
% 11.26/2.01  ------ SAT Options
% 11.26/2.01  
% 11.26/2.01  --sat_mode                              false
% 11.26/2.01  --sat_fm_restart_options                ""
% 11.26/2.01  --sat_gr_def                            false
% 11.26/2.01  --sat_epr_types                         true
% 11.26/2.01  --sat_non_cyclic_types                  false
% 11.26/2.01  --sat_finite_models                     false
% 11.26/2.01  --sat_fm_lemmas                         false
% 11.26/2.01  --sat_fm_prep                           false
% 11.26/2.01  --sat_fm_uc_incr                        true
% 11.26/2.01  --sat_out_model                         small
% 11.26/2.01  --sat_out_clauses                       false
% 11.26/2.01  
% 11.26/2.01  ------ QBF Options
% 11.26/2.01  
% 11.26/2.01  --qbf_mode                              false
% 11.26/2.01  --qbf_elim_univ                         false
% 11.26/2.01  --qbf_dom_inst                          none
% 11.26/2.01  --qbf_dom_pre_inst                      false
% 11.26/2.01  --qbf_sk_in                             false
% 11.26/2.01  --qbf_pred_elim                         true
% 11.26/2.01  --qbf_split                             512
% 11.26/2.01  
% 11.26/2.01  ------ BMC1 Options
% 11.26/2.01  
% 11.26/2.01  --bmc1_incremental                      false
% 11.26/2.01  --bmc1_axioms                           reachable_all
% 11.26/2.01  --bmc1_min_bound                        0
% 11.26/2.01  --bmc1_max_bound                        -1
% 11.26/2.01  --bmc1_max_bound_default                -1
% 11.26/2.01  --bmc1_symbol_reachability              true
% 11.26/2.01  --bmc1_property_lemmas                  false
% 11.26/2.01  --bmc1_k_induction                      false
% 11.26/2.01  --bmc1_non_equiv_states                 false
% 11.26/2.01  --bmc1_deadlock                         false
% 11.26/2.01  --bmc1_ucm                              false
% 11.26/2.01  --bmc1_add_unsat_core                   none
% 11.26/2.01  --bmc1_unsat_core_children              false
% 11.26/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.26/2.01  --bmc1_out_stat                         full
% 11.26/2.01  --bmc1_ground_init                      false
% 11.26/2.01  --bmc1_pre_inst_next_state              false
% 11.26/2.01  --bmc1_pre_inst_state                   false
% 11.26/2.01  --bmc1_pre_inst_reach_state             false
% 11.26/2.01  --bmc1_out_unsat_core                   false
% 11.26/2.01  --bmc1_aig_witness_out                  false
% 11.26/2.01  --bmc1_verbose                          false
% 11.26/2.01  --bmc1_dump_clauses_tptp                false
% 11.26/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.26/2.01  --bmc1_dump_file                        -
% 11.26/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.26/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.26/2.01  --bmc1_ucm_extend_mode                  1
% 11.26/2.01  --bmc1_ucm_init_mode                    2
% 11.26/2.01  --bmc1_ucm_cone_mode                    none
% 11.26/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.26/2.01  --bmc1_ucm_relax_model                  4
% 11.26/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.26/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.26/2.01  --bmc1_ucm_layered_model                none
% 11.26/2.01  --bmc1_ucm_max_lemma_size               10
% 11.26/2.01  
% 11.26/2.01  ------ AIG Options
% 11.26/2.01  
% 11.26/2.01  --aig_mode                              false
% 11.26/2.01  
% 11.26/2.01  ------ Instantiation Options
% 11.26/2.01  
% 11.26/2.01  --instantiation_flag                    true
% 11.26/2.01  --inst_sos_flag                         false
% 11.26/2.01  --inst_sos_phase                        true
% 11.26/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.26/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.26/2.01  --inst_lit_sel_side                     num_symb
% 11.26/2.01  --inst_solver_per_active                1400
% 11.26/2.01  --inst_solver_calls_frac                1.
% 11.26/2.01  --inst_passive_queue_type               priority_queues
% 11.26/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.26/2.01  --inst_passive_queues_freq              [25;2]
% 11.26/2.01  --inst_dismatching                      true
% 11.26/2.01  --inst_eager_unprocessed_to_passive     true
% 11.26/2.01  --inst_prop_sim_given                   true
% 11.26/2.01  --inst_prop_sim_new                     false
% 11.26/2.01  --inst_subs_new                         false
% 11.26/2.01  --inst_eq_res_simp                      false
% 11.26/2.01  --inst_subs_given                       false
% 11.26/2.01  --inst_orphan_elimination               true
% 11.26/2.01  --inst_learning_loop_flag               true
% 11.26/2.01  --inst_learning_start                   3000
% 11.26/2.01  --inst_learning_factor                  2
% 11.26/2.01  --inst_start_prop_sim_after_learn       3
% 11.26/2.01  --inst_sel_renew                        solver
% 11.26/2.01  --inst_lit_activity_flag                true
% 11.26/2.01  --inst_restr_to_given                   false
% 11.26/2.01  --inst_activity_threshold               500
% 11.26/2.01  --inst_out_proof                        true
% 11.26/2.01  
% 11.26/2.01  ------ Resolution Options
% 11.26/2.01  
% 11.26/2.01  --resolution_flag                       true
% 11.26/2.01  --res_lit_sel                           adaptive
% 11.26/2.01  --res_lit_sel_side                      none
% 11.26/2.01  --res_ordering                          kbo
% 11.26/2.01  --res_to_prop_solver                    active
% 11.26/2.01  --res_prop_simpl_new                    false
% 11.26/2.01  --res_prop_simpl_given                  true
% 11.26/2.01  --res_passive_queue_type                priority_queues
% 11.26/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.26/2.01  --res_passive_queues_freq               [15;5]
% 11.26/2.01  --res_forward_subs                      full
% 11.26/2.01  --res_backward_subs                     full
% 11.26/2.01  --res_forward_subs_resolution           true
% 11.26/2.01  --res_backward_subs_resolution          true
% 11.26/2.01  --res_orphan_elimination                true
% 11.26/2.01  --res_time_limit                        2.
% 11.26/2.01  --res_out_proof                         true
% 11.26/2.01  
% 11.26/2.01  ------ Superposition Options
% 11.26/2.01  
% 11.26/2.01  --superposition_flag                    true
% 11.26/2.01  --sup_passive_queue_type                priority_queues
% 11.26/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.26/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.26/2.01  --demod_completeness_check              fast
% 11.26/2.01  --demod_use_ground                      true
% 11.26/2.01  --sup_to_prop_solver                    passive
% 11.26/2.01  --sup_prop_simpl_new                    true
% 11.26/2.01  --sup_prop_simpl_given                  true
% 11.26/2.01  --sup_fun_splitting                     false
% 11.26/2.01  --sup_smt_interval                      50000
% 11.26/2.01  
% 11.26/2.01  ------ Superposition Simplification Setup
% 11.26/2.01  
% 11.26/2.01  --sup_indices_passive                   []
% 11.26/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.26/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.26/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.26/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.26/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.26/2.01  --sup_full_bw                           [BwDemod]
% 11.26/2.01  --sup_immed_triv                        [TrivRules]
% 11.26/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.26/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.26/2.01  --sup_immed_bw_main                     []
% 11.26/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.26/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.26/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.26/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.26/2.01  
% 11.26/2.01  ------ Combination Options
% 11.26/2.01  
% 11.26/2.01  --comb_res_mult                         3
% 11.26/2.01  --comb_sup_mult                         2
% 11.26/2.01  --comb_inst_mult                        10
% 11.26/2.01  
% 11.26/2.01  ------ Debug Options
% 11.26/2.01  
% 11.26/2.01  --dbg_backtrace                         false
% 11.26/2.01  --dbg_dump_prop_clauses                 false
% 11.26/2.01  --dbg_dump_prop_clauses_file            -
% 11.26/2.01  --dbg_out_stat                          false
% 11.26/2.01  ------ Parsing...
% 11.26/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.26/2.01  
% 11.26/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.26/2.01  
% 11.26/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.26/2.01  
% 11.26/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.26/2.01  ------ Proving...
% 11.26/2.01  ------ Problem Properties 
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  clauses                                 30
% 11.26/2.01  conjectures                             8
% 11.26/2.01  EPR                                     6
% 11.26/2.01  Horn                                    30
% 11.26/2.01  unary                                   10
% 11.26/2.01  binary                                  4
% 11.26/2.01  lits                                    94
% 11.26/2.01  lits eq                                 14
% 11.26/2.01  fd_pure                                 0
% 11.26/2.01  fd_pseudo                               0
% 11.26/2.01  fd_cond                                 0
% 11.26/2.01  fd_pseudo_cond                          2
% 11.26/2.01  AC symbols                              0
% 11.26/2.01  
% 11.26/2.01  ------ Schedule dynamic 5 is on 
% 11.26/2.01  
% 11.26/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  ------ 
% 11.26/2.01  Current options:
% 11.26/2.01  ------ 
% 11.26/2.01  
% 11.26/2.01  ------ Input Options
% 11.26/2.01  
% 11.26/2.01  --out_options                           all
% 11.26/2.01  --tptp_safe_out                         true
% 11.26/2.01  --problem_path                          ""
% 11.26/2.01  --include_path                          ""
% 11.26/2.01  --clausifier                            res/vclausify_rel
% 11.26/2.01  --clausifier_options                    --mode clausify
% 11.26/2.01  --stdin                                 false
% 11.26/2.01  --stats_out                             all
% 11.26/2.01  
% 11.26/2.01  ------ General Options
% 11.26/2.01  
% 11.26/2.01  --fof                                   false
% 11.26/2.01  --time_out_real                         305.
% 11.26/2.01  --time_out_virtual                      -1.
% 11.26/2.01  --symbol_type_check                     false
% 11.26/2.01  --clausify_out                          false
% 11.26/2.01  --sig_cnt_out                           false
% 11.26/2.01  --trig_cnt_out                          false
% 11.26/2.01  --trig_cnt_out_tolerance                1.
% 11.26/2.01  --trig_cnt_out_sk_spl                   false
% 11.26/2.01  --abstr_cl_out                          false
% 11.26/2.01  
% 11.26/2.01  ------ Global Options
% 11.26/2.01  
% 11.26/2.01  --schedule                              default
% 11.26/2.01  --add_important_lit                     false
% 11.26/2.01  --prop_solver_per_cl                    1000
% 11.26/2.01  --min_unsat_core                        false
% 11.26/2.01  --soft_assumptions                      false
% 11.26/2.01  --soft_lemma_size                       3
% 11.26/2.01  --prop_impl_unit_size                   0
% 11.26/2.01  --prop_impl_unit                        []
% 11.26/2.01  --share_sel_clauses                     true
% 11.26/2.01  --reset_solvers                         false
% 11.26/2.01  --bc_imp_inh                            [conj_cone]
% 11.26/2.01  --conj_cone_tolerance                   3.
% 11.26/2.01  --extra_neg_conj                        none
% 11.26/2.01  --large_theory_mode                     true
% 11.26/2.01  --prolific_symb_bound                   200
% 11.26/2.01  --lt_threshold                          2000
% 11.26/2.01  --clause_weak_htbl                      true
% 11.26/2.01  --gc_record_bc_elim                     false
% 11.26/2.01  
% 11.26/2.01  ------ Preprocessing Options
% 11.26/2.01  
% 11.26/2.01  --preprocessing_flag                    true
% 11.26/2.01  --time_out_prep_mult                    0.1
% 11.26/2.01  --splitting_mode                        input
% 11.26/2.01  --splitting_grd                         true
% 11.26/2.01  --splitting_cvd                         false
% 11.26/2.01  --splitting_cvd_svl                     false
% 11.26/2.01  --splitting_nvd                         32
% 11.26/2.01  --sub_typing                            true
% 11.26/2.01  --prep_gs_sim                           true
% 11.26/2.01  --prep_unflatten                        true
% 11.26/2.01  --prep_res_sim                          true
% 11.26/2.01  --prep_upred                            true
% 11.26/2.01  --prep_sem_filter                       exhaustive
% 11.26/2.01  --prep_sem_filter_out                   false
% 11.26/2.01  --pred_elim                             true
% 11.26/2.01  --res_sim_input                         true
% 11.26/2.01  --eq_ax_congr_red                       true
% 11.26/2.01  --pure_diseq_elim                       true
% 11.26/2.01  --brand_transform                       false
% 11.26/2.01  --non_eq_to_eq                          false
% 11.26/2.01  --prep_def_merge                        true
% 11.26/2.01  --prep_def_merge_prop_impl              false
% 11.26/2.01  --prep_def_merge_mbd                    true
% 11.26/2.01  --prep_def_merge_tr_red                 false
% 11.26/2.01  --prep_def_merge_tr_cl                  false
% 11.26/2.01  --smt_preprocessing                     true
% 11.26/2.01  --smt_ac_axioms                         fast
% 11.26/2.01  --preprocessed_out                      false
% 11.26/2.01  --preprocessed_stats                    false
% 11.26/2.01  
% 11.26/2.01  ------ Abstraction refinement Options
% 11.26/2.01  
% 11.26/2.01  --abstr_ref                             []
% 11.26/2.01  --abstr_ref_prep                        false
% 11.26/2.01  --abstr_ref_until_sat                   false
% 11.26/2.01  --abstr_ref_sig_restrict                funpre
% 11.26/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.26/2.01  --abstr_ref_under                       []
% 11.26/2.01  
% 11.26/2.01  ------ SAT Options
% 11.26/2.01  
% 11.26/2.01  --sat_mode                              false
% 11.26/2.01  --sat_fm_restart_options                ""
% 11.26/2.01  --sat_gr_def                            false
% 11.26/2.01  --sat_epr_types                         true
% 11.26/2.01  --sat_non_cyclic_types                  false
% 11.26/2.01  --sat_finite_models                     false
% 11.26/2.01  --sat_fm_lemmas                         false
% 11.26/2.01  --sat_fm_prep                           false
% 11.26/2.01  --sat_fm_uc_incr                        true
% 11.26/2.01  --sat_out_model                         small
% 11.26/2.01  --sat_out_clauses                       false
% 11.26/2.01  
% 11.26/2.01  ------ QBF Options
% 11.26/2.01  
% 11.26/2.01  --qbf_mode                              false
% 11.26/2.01  --qbf_elim_univ                         false
% 11.26/2.01  --qbf_dom_inst                          none
% 11.26/2.01  --qbf_dom_pre_inst                      false
% 11.26/2.01  --qbf_sk_in                             false
% 11.26/2.01  --qbf_pred_elim                         true
% 11.26/2.01  --qbf_split                             512
% 11.26/2.01  
% 11.26/2.01  ------ BMC1 Options
% 11.26/2.01  
% 11.26/2.01  --bmc1_incremental                      false
% 11.26/2.01  --bmc1_axioms                           reachable_all
% 11.26/2.01  --bmc1_min_bound                        0
% 11.26/2.01  --bmc1_max_bound                        -1
% 11.26/2.01  --bmc1_max_bound_default                -1
% 11.26/2.01  --bmc1_symbol_reachability              true
% 11.26/2.01  --bmc1_property_lemmas                  false
% 11.26/2.01  --bmc1_k_induction                      false
% 11.26/2.01  --bmc1_non_equiv_states                 false
% 11.26/2.01  --bmc1_deadlock                         false
% 11.26/2.01  --bmc1_ucm                              false
% 11.26/2.01  --bmc1_add_unsat_core                   none
% 11.26/2.01  --bmc1_unsat_core_children              false
% 11.26/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.26/2.01  --bmc1_out_stat                         full
% 11.26/2.01  --bmc1_ground_init                      false
% 11.26/2.01  --bmc1_pre_inst_next_state              false
% 11.26/2.01  --bmc1_pre_inst_state                   false
% 11.26/2.01  --bmc1_pre_inst_reach_state             false
% 11.26/2.01  --bmc1_out_unsat_core                   false
% 11.26/2.01  --bmc1_aig_witness_out                  false
% 11.26/2.01  --bmc1_verbose                          false
% 11.26/2.01  --bmc1_dump_clauses_tptp                false
% 11.26/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.26/2.01  --bmc1_dump_file                        -
% 11.26/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.26/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.26/2.01  --bmc1_ucm_extend_mode                  1
% 11.26/2.01  --bmc1_ucm_init_mode                    2
% 11.26/2.01  --bmc1_ucm_cone_mode                    none
% 11.26/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.26/2.01  --bmc1_ucm_relax_model                  4
% 11.26/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.26/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.26/2.01  --bmc1_ucm_layered_model                none
% 11.26/2.01  --bmc1_ucm_max_lemma_size               10
% 11.26/2.01  
% 11.26/2.01  ------ AIG Options
% 11.26/2.01  
% 11.26/2.01  --aig_mode                              false
% 11.26/2.01  
% 11.26/2.01  ------ Instantiation Options
% 11.26/2.01  
% 11.26/2.01  --instantiation_flag                    true
% 11.26/2.01  --inst_sos_flag                         false
% 11.26/2.01  --inst_sos_phase                        true
% 11.26/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.26/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.26/2.01  --inst_lit_sel_side                     none
% 11.26/2.01  --inst_solver_per_active                1400
% 11.26/2.01  --inst_solver_calls_frac                1.
% 11.26/2.01  --inst_passive_queue_type               priority_queues
% 11.26/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.26/2.01  --inst_passive_queues_freq              [25;2]
% 11.26/2.01  --inst_dismatching                      true
% 11.26/2.01  --inst_eager_unprocessed_to_passive     true
% 11.26/2.01  --inst_prop_sim_given                   true
% 11.26/2.01  --inst_prop_sim_new                     false
% 11.26/2.01  --inst_subs_new                         false
% 11.26/2.01  --inst_eq_res_simp                      false
% 11.26/2.01  --inst_subs_given                       false
% 11.26/2.01  --inst_orphan_elimination               true
% 11.26/2.01  --inst_learning_loop_flag               true
% 11.26/2.01  --inst_learning_start                   3000
% 11.26/2.01  --inst_learning_factor                  2
% 11.26/2.01  --inst_start_prop_sim_after_learn       3
% 11.26/2.01  --inst_sel_renew                        solver
% 11.26/2.01  --inst_lit_activity_flag                true
% 11.26/2.01  --inst_restr_to_given                   false
% 11.26/2.01  --inst_activity_threshold               500
% 11.26/2.01  --inst_out_proof                        true
% 11.26/2.01  
% 11.26/2.01  ------ Resolution Options
% 11.26/2.01  
% 11.26/2.01  --resolution_flag                       false
% 11.26/2.01  --res_lit_sel                           adaptive
% 11.26/2.01  --res_lit_sel_side                      none
% 11.26/2.01  --res_ordering                          kbo
% 11.26/2.01  --res_to_prop_solver                    active
% 11.26/2.01  --res_prop_simpl_new                    false
% 11.26/2.01  --res_prop_simpl_given                  true
% 11.26/2.01  --res_passive_queue_type                priority_queues
% 11.26/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.26/2.01  --res_passive_queues_freq               [15;5]
% 11.26/2.01  --res_forward_subs                      full
% 11.26/2.01  --res_backward_subs                     full
% 11.26/2.01  --res_forward_subs_resolution           true
% 11.26/2.01  --res_backward_subs_resolution          true
% 11.26/2.01  --res_orphan_elimination                true
% 11.26/2.01  --res_time_limit                        2.
% 11.26/2.01  --res_out_proof                         true
% 11.26/2.01  
% 11.26/2.01  ------ Superposition Options
% 11.26/2.01  
% 11.26/2.01  --superposition_flag                    true
% 11.26/2.01  --sup_passive_queue_type                priority_queues
% 11.26/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.26/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.26/2.01  --demod_completeness_check              fast
% 11.26/2.01  --demod_use_ground                      true
% 11.26/2.01  --sup_to_prop_solver                    passive
% 11.26/2.01  --sup_prop_simpl_new                    true
% 11.26/2.01  --sup_prop_simpl_given                  true
% 11.26/2.01  --sup_fun_splitting                     false
% 11.26/2.01  --sup_smt_interval                      50000
% 11.26/2.01  
% 11.26/2.01  ------ Superposition Simplification Setup
% 11.26/2.01  
% 11.26/2.01  --sup_indices_passive                   []
% 11.26/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.26/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.26/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.26/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.26/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.26/2.01  --sup_full_bw                           [BwDemod]
% 11.26/2.01  --sup_immed_triv                        [TrivRules]
% 11.26/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.26/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.26/2.01  --sup_immed_bw_main                     []
% 11.26/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.26/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.26/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.26/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.26/2.01  
% 11.26/2.01  ------ Combination Options
% 11.26/2.01  
% 11.26/2.01  --comb_res_mult                         3
% 11.26/2.01  --comb_sup_mult                         2
% 11.26/2.01  --comb_inst_mult                        10
% 11.26/2.01  
% 11.26/2.01  ------ Debug Options
% 11.26/2.01  
% 11.26/2.01  --dbg_backtrace                         false
% 11.26/2.01  --dbg_dump_prop_clauses                 false
% 11.26/2.01  --dbg_dump_prop_clauses_file            -
% 11.26/2.01  --dbg_out_stat                          false
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  ------ Proving...
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  % SZS status Theorem for theBenchmark.p
% 11.26/2.01  
% 11.26/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.26/2.01  
% 11.26/2.01  fof(f17,conjecture,(
% 11.26/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f18,negated_conjecture,(
% 11.26/2.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 11.26/2.01    inference(negated_conjecture,[],[f17])).
% 11.26/2.01  
% 11.26/2.01  fof(f44,plain,(
% 11.26/2.01    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 11.26/2.01    inference(ennf_transformation,[],[f18])).
% 11.26/2.01  
% 11.26/2.01  fof(f45,plain,(
% 11.26/2.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 11.26/2.01    inference(flattening,[],[f44])).
% 11.26/2.01  
% 11.26/2.01  fof(f49,plain,(
% 11.26/2.01    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 11.26/2.01    introduced(choice_axiom,[])).
% 11.26/2.01  
% 11.26/2.01  fof(f48,plain,(
% 11.26/2.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 11.26/2.01    introduced(choice_axiom,[])).
% 11.26/2.01  
% 11.26/2.01  fof(f50,plain,(
% 11.26/2.01    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 11.26/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f49,f48])).
% 11.26/2.01  
% 11.26/2.01  fof(f84,plain,(
% 11.26/2.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f15,axiom,(
% 11.26/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f42,plain,(
% 11.26/2.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 11.26/2.01    inference(ennf_transformation,[],[f15])).
% 11.26/2.01  
% 11.26/2.01  fof(f43,plain,(
% 11.26/2.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 11.26/2.01    inference(flattening,[],[f42])).
% 11.26/2.01  
% 11.26/2.01  fof(f75,plain,(
% 11.26/2.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f43])).
% 11.26/2.01  
% 11.26/2.01  fof(f81,plain,(
% 11.26/2.01    v1_funct_1(sK2)),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f82,plain,(
% 11.26/2.01    v1_funct_2(sK2,sK0,sK0)),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f83,plain,(
% 11.26/2.01    v3_funct_2(sK2,sK0,sK0)),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f12,axiom,(
% 11.26/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f38,plain,(
% 11.26/2.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 11.26/2.01    inference(ennf_transformation,[],[f12])).
% 11.26/2.01  
% 11.26/2.01  fof(f39,plain,(
% 11.26/2.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 11.26/2.01    inference(flattening,[],[f38])).
% 11.26/2.01  
% 11.26/2.01  fof(f72,plain,(
% 11.26/2.01    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f39])).
% 11.26/2.01  
% 11.26/2.01  fof(f9,axiom,(
% 11.26/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f32,plain,(
% 11.26/2.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.26/2.01    inference(ennf_transformation,[],[f9])).
% 11.26/2.01  
% 11.26/2.01  fof(f33,plain,(
% 11.26/2.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.26/2.01    inference(flattening,[],[f32])).
% 11.26/2.01  
% 11.26/2.01  fof(f64,plain,(
% 11.26/2.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.26/2.01    inference(cnf_transformation,[],[f33])).
% 11.26/2.01  
% 11.26/2.01  fof(f7,axiom,(
% 11.26/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f20,plain,(
% 11.26/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.26/2.01    inference(pure_predicate_removal,[],[f7])).
% 11.26/2.01  
% 11.26/2.01  fof(f29,plain,(
% 11.26/2.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.26/2.01    inference(ennf_transformation,[],[f20])).
% 11.26/2.01  
% 11.26/2.01  fof(f59,plain,(
% 11.26/2.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.26/2.01    inference(cnf_transformation,[],[f29])).
% 11.26/2.01  
% 11.26/2.01  fof(f10,axiom,(
% 11.26/2.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f34,plain,(
% 11.26/2.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.26/2.01    inference(ennf_transformation,[],[f10])).
% 11.26/2.01  
% 11.26/2.01  fof(f35,plain,(
% 11.26/2.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.26/2.01    inference(flattening,[],[f34])).
% 11.26/2.01  
% 11.26/2.01  fof(f47,plain,(
% 11.26/2.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.26/2.01    inference(nnf_transformation,[],[f35])).
% 11.26/2.01  
% 11.26/2.01  fof(f65,plain,(
% 11.26/2.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f47])).
% 11.26/2.01  
% 11.26/2.01  fof(f6,axiom,(
% 11.26/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f28,plain,(
% 11.26/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.26/2.01    inference(ennf_transformation,[],[f6])).
% 11.26/2.01  
% 11.26/2.01  fof(f58,plain,(
% 11.26/2.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.26/2.01    inference(cnf_transformation,[],[f28])).
% 11.26/2.01  
% 11.26/2.01  fof(f63,plain,(
% 11.26/2.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.26/2.01    inference(cnf_transformation,[],[f33])).
% 11.26/2.01  
% 11.26/2.01  fof(f3,axiom,(
% 11.26/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f22,plain,(
% 11.26/2.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.26/2.01    inference(ennf_transformation,[],[f3])).
% 11.26/2.01  
% 11.26/2.01  fof(f23,plain,(
% 11.26/2.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.26/2.01    inference(flattening,[],[f22])).
% 11.26/2.01  
% 11.26/2.01  fof(f54,plain,(
% 11.26/2.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f23])).
% 11.26/2.01  
% 11.26/2.01  fof(f4,axiom,(
% 11.26/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f24,plain,(
% 11.26/2.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.26/2.01    inference(ennf_transformation,[],[f4])).
% 11.26/2.01  
% 11.26/2.01  fof(f25,plain,(
% 11.26/2.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.26/2.01    inference(flattening,[],[f24])).
% 11.26/2.01  
% 11.26/2.01  fof(f55,plain,(
% 11.26/2.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f25])).
% 11.26/2.01  
% 11.26/2.01  fof(f16,axiom,(
% 11.26/2.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f76,plain,(
% 11.26/2.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f16])).
% 11.26/2.01  
% 11.26/2.01  fof(f88,plain,(
% 11.26/2.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.26/2.01    inference(definition_unfolding,[],[f55,f76])).
% 11.26/2.01  
% 11.26/2.01  fof(f5,axiom,(
% 11.26/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f26,plain,(
% 11.26/2.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.26/2.01    inference(ennf_transformation,[],[f5])).
% 11.26/2.01  
% 11.26/2.01  fof(f27,plain,(
% 11.26/2.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.26/2.01    inference(flattening,[],[f26])).
% 11.26/2.01  
% 11.26/2.01  fof(f57,plain,(
% 11.26/2.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f27])).
% 11.26/2.01  
% 11.26/2.01  fof(f89,plain,(
% 11.26/2.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.26/2.01    inference(definition_unfolding,[],[f57,f76])).
% 11.26/2.01  
% 11.26/2.01  fof(f53,plain,(
% 11.26/2.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f23])).
% 11.26/2.01  
% 11.26/2.01  fof(f69,plain,(
% 11.26/2.01    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f39])).
% 11.26/2.01  
% 11.26/2.01  fof(f80,plain,(
% 11.26/2.01    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f14,axiom,(
% 11.26/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f40,plain,(
% 11.26/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.26/2.01    inference(ennf_transformation,[],[f14])).
% 11.26/2.01  
% 11.26/2.01  fof(f41,plain,(
% 11.26/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.26/2.01    inference(flattening,[],[f40])).
% 11.26/2.01  
% 11.26/2.01  fof(f74,plain,(
% 11.26/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f41])).
% 11.26/2.01  
% 11.26/2.01  fof(f8,axiom,(
% 11.26/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f30,plain,(
% 11.26/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.26/2.01    inference(ennf_transformation,[],[f8])).
% 11.26/2.01  
% 11.26/2.01  fof(f31,plain,(
% 11.26/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.26/2.01    inference(flattening,[],[f30])).
% 11.26/2.01  
% 11.26/2.01  fof(f46,plain,(
% 11.26/2.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.26/2.01    inference(nnf_transformation,[],[f31])).
% 11.26/2.01  
% 11.26/2.01  fof(f60,plain,(
% 11.26/2.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.26/2.01    inference(cnf_transformation,[],[f46])).
% 11.26/2.01  
% 11.26/2.01  fof(f85,plain,(
% 11.26/2.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f13,axiom,(
% 11.26/2.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f19,plain,(
% 11.26/2.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.26/2.01    inference(pure_predicate_removal,[],[f13])).
% 11.26/2.01  
% 11.26/2.01  fof(f73,plain,(
% 11.26/2.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.26/2.01    inference(cnf_transformation,[],[f19])).
% 11.26/2.01  
% 11.26/2.01  fof(f77,plain,(
% 11.26/2.01    v1_funct_1(sK1)),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f11,axiom,(
% 11.26/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.26/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.26/2.01  
% 11.26/2.01  fof(f36,plain,(
% 11.26/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.26/2.01    inference(ennf_transformation,[],[f11])).
% 11.26/2.01  
% 11.26/2.01  fof(f37,plain,(
% 11.26/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.26/2.01    inference(flattening,[],[f36])).
% 11.26/2.01  
% 11.26/2.01  fof(f68,plain,(
% 11.26/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f37])).
% 11.26/2.01  
% 11.26/2.01  fof(f79,plain,(
% 11.26/2.01    v3_funct_2(sK1,sK0,sK0)),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f70,plain,(
% 11.26/2.01    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f39])).
% 11.26/2.01  
% 11.26/2.01  fof(f71,plain,(
% 11.26/2.01    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.26/2.01    inference(cnf_transformation,[],[f39])).
% 11.26/2.01  
% 11.26/2.01  fof(f61,plain,(
% 11.26/2.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.26/2.01    inference(cnf_transformation,[],[f46])).
% 11.26/2.01  
% 11.26/2.01  fof(f90,plain,(
% 11.26/2.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.26/2.01    inference(equality_resolution,[],[f61])).
% 11.26/2.01  
% 11.26/2.01  fof(f86,plain,(
% 11.26/2.01    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  fof(f78,plain,(
% 11.26/2.01    v1_funct_2(sK1,sK0,sK0)),
% 11.26/2.01    inference(cnf_transformation,[],[f50])).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1016,plain,
% 11.26/2.01      ( X0_50 != X1_50
% 11.26/2.01      | X0_49 != X1_49
% 11.26/2.01      | k2_funct_2(X0_50,X0_49) = k2_funct_2(X1_50,X1_49) ),
% 11.26/2.01      theory(equality) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2042,plain,
% 11.26/2.01      ( sK0 != X0_50
% 11.26/2.01      | k2_funct_2(sK0,sK1) = k2_funct_2(X0_50,X0_49)
% 11.26/2.01      | sK1 != X0_49 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1016]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_54719,plain,
% 11.26/2.01      ( sK0 != X0_50
% 11.26/2.01      | k2_funct_2(sK0,sK1) = k2_funct_2(X0_50,k2_funct_1(sK2))
% 11.26/2.01      | sK1 != k2_funct_1(sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2042]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_54720,plain,
% 11.26/2.01      ( sK0 != sK0
% 11.26/2.01      | k2_funct_2(sK0,sK1) = k2_funct_2(sK0,k2_funct_1(sK2))
% 11.26/2.01      | sK1 != k2_funct_1(sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_54719]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1003,plain,
% 11.26/2.01      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 11.26/2.01      theory(equality) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1940,plain,
% 11.26/2.01      ( X0_49 != X1_49
% 11.26/2.01      | X0_49 = k2_funct_2(X0_50,X2_49)
% 11.26/2.01      | k2_funct_2(X0_50,X2_49) != X1_49 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1003]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2116,plain,
% 11.26/2.01      ( X0_49 != k2_funct_2(X0_50,X1_49)
% 11.26/2.01      | X0_49 = k2_funct_2(X1_50,X2_49)
% 11.26/2.01      | k2_funct_2(X1_50,X2_49) != k2_funct_2(X0_50,X1_49) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1940]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_29137,plain,
% 11.26/2.01      ( k2_funct_2(X0_50,X0_49) != k2_funct_2(X1_50,k2_funct_1(sK2))
% 11.26/2.01      | sK2 = k2_funct_2(X0_50,X0_49)
% 11.26/2.01      | sK2 != k2_funct_2(X1_50,k2_funct_1(sK2)) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2116]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_29143,plain,
% 11.26/2.01      ( k2_funct_2(sK0,sK1) != k2_funct_2(sK0,k2_funct_1(sK2))
% 11.26/2.01      | sK2 != k2_funct_2(sK0,k2_funct_1(sK2))
% 11.26/2.01      | sK2 = k2_funct_2(sK0,sK1) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_29137]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2569,plain,
% 11.26/2.01      ( X0_49 != X1_49
% 11.26/2.01      | X0_49 = k2_funct_1(X2_49)
% 11.26/2.01      | k2_funct_1(X2_49) != X1_49 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1003]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_20094,plain,
% 11.26/2.01      ( X0_49 = k2_funct_1(sK2) | X0_49 != sK1 | k2_funct_1(sK2) != sK1 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2569]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_20096,plain,
% 11.26/2.01      ( k2_funct_1(sK2) != sK1 | sK1 = k2_funct_1(sK2) | sK1 != sK1 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_20094]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2112,plain,
% 11.26/2.01      ( X0_49 = k2_funct_2(X0_50,X1_49)
% 11.26/2.01      | X0_49 != k2_funct_1(X1_49)
% 11.26/2.01      | k2_funct_2(X0_50,X1_49) != k2_funct_1(X1_49) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1940]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_17737,plain,
% 11.26/2.01      ( k2_funct_2(X0_50,k2_funct_1(sK2)) != k2_funct_1(k2_funct_1(sK2))
% 11.26/2.01      | sK2 = k2_funct_2(X0_50,k2_funct_1(sK2))
% 11.26/2.01      | sK2 != k2_funct_1(k2_funct_1(sK2)) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2112]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_17738,plain,
% 11.26/2.01      ( k2_funct_2(sK0,k2_funct_1(sK2)) != k2_funct_1(k2_funct_1(sK2))
% 11.26/2.01      | sK2 = k2_funct_2(sK0,k2_funct_1(sK2))
% 11.26/2.01      | sK2 != k2_funct_1(k2_funct_1(sK2)) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_17737]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1922,plain,
% 11.26/2.01      ( X0_49 != X1_49 | sK2 != X1_49 | sK2 = X0_49 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1003]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2001,plain,
% 11.26/2.01      ( X0_49 != sK2 | sK2 = X0_49 | sK2 != sK2 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1922]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8834,plain,
% 11.26/2.01      ( k2_funct_1(k2_funct_1(sK2)) != sK2
% 11.26/2.01      | sK2 = k2_funct_1(k2_funct_1(sK2))
% 11.26/2.01      | sK2 != sK2 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2001]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_27,negated_conjecture,
% 11.26/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.26/2.01      inference(cnf_transformation,[],[f84]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_980,negated_conjecture,
% 11.26/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_27]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1551,plain,
% 11.26/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_24,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ v3_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.26/2.01      | ~ v1_funct_1(X0)
% 11.26/2.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_981,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49)
% 11.26/2.01      | k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_24]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1550,plain,
% 11.26/2.01      ( k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49)
% 11.26/2.01      | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2911,plain,
% 11.26/2.01      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 11.26/2.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1550]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_30,negated_conjecture,
% 11.26/2.01      ( v1_funct_1(sK2) ),
% 11.26/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_39,plain,
% 11.26/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_29,negated_conjecture,
% 11.26/2.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_40,plain,
% 11.26/2.01      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_28,negated_conjecture,
% 11.26/2.01      ( v3_funct_2(sK2,sK0,sK0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f83]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_41,plain,
% 11.26/2.01      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3486,plain,
% 11.26/2.01      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2911,c_39,c_40,c_41]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_18,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ v3_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.26/2.01      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.26/2.01      | ~ v1_funct_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_987,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 11.26/2.01      | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_18]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1544,plain,
% 11.26/2.01      ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 11.26/2.01      | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3867,plain,
% 11.26/2.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 11.26/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_3486,c_1544]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_42,plain,
% 11.26/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8316,plain,
% 11.26/2.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_3867,c_39,c_40,c_41,c_42]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_11,plain,
% 11.26/2.01      ( ~ v3_funct_2(X0,X1,X2)
% 11.26/2.01      | v2_funct_2(X0,X2)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | ~ v1_funct_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8,plain,
% 11.26/2.01      ( v5_relat_1(X0,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.26/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_15,plain,
% 11.26/2.01      ( ~ v2_funct_2(X0,X1)
% 11.26/2.01      | ~ v5_relat_1(X0,X1)
% 11.26/2.01      | ~ v1_relat_1(X0)
% 11.26/2.01      | k2_relat_1(X0) = X1 ),
% 11.26/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_378,plain,
% 11.26/2.01      ( ~ v2_funct_2(X0,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.26/2.01      | ~ v1_relat_1(X0)
% 11.26/2.01      | k2_relat_1(X0) = X1 ),
% 11.26/2.01      inference(resolution,[status(thm)],[c_8,c_15]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_7,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | v1_relat_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_390,plain,
% 11.26/2.01      ( ~ v2_funct_2(X0,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.26/2.01      | k2_relat_1(X0) = X1 ),
% 11.26/2.01      inference(forward_subsumption_resolution,[status(thm)],[c_378,c_7]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_466,plain,
% 11.26/2.01      ( ~ v3_funct_2(X0,X1,X2)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.26/2.01      | ~ v1_funct_1(X0)
% 11.26/2.01      | X3 != X0
% 11.26/2.01      | X5 != X2
% 11.26/2.01      | k2_relat_1(X3) = X5 ),
% 11.26/2.01      inference(resolution_lifted,[status(thm)],[c_11,c_390]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_467,plain,
% 11.26/2.01      ( ~ v3_funct_2(X0,X1,X2)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.26/2.01      | ~ v1_funct_1(X0)
% 11.26/2.01      | k2_relat_1(X0) = X2 ),
% 11.26/2.01      inference(unflattening,[status(thm)],[c_466]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_970,plain,
% 11.26/2.01      ( ~ v3_funct_2(X0_49,X0_50,X1_50)
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49)
% 11.26/2.01      | k2_relat_1(X0_49) = X1_50 ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_467]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1561,plain,
% 11.26/2.01      ( k2_relat_1(X0_49) = X0_50
% 11.26/2.01      | v3_funct_2(X0_49,X1_50,X0_50) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X0_50))) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8331,plain,
% 11.26/2.01      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 11.26/2.01      | v3_funct_2(k2_funct_1(sK2),X0_50,sK0) != iProver_top
% 11.26/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_8316,c_1561]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_12,plain,
% 11.26/2.01      ( ~ v3_funct_2(X0,X1,X2)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | ~ v1_funct_1(X0)
% 11.26/2.01      | v2_funct_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_990,plain,
% 11.26/2.01      ( ~ v3_funct_2(X0_49,X0_50,X1_50)
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49)
% 11.26/2.01      | v2_funct_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_12]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1541,plain,
% 11.26/2.01      ( v3_funct_2(X0_49,X0_50,X1_50) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v2_funct_1(X0_49) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_990]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2422,plain,
% 11.26/2.01      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top
% 11.26/2.01      | v2_funct_1(sK2) = iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1541]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2673,plain,
% 11.26/2.01      ( v2_funct_1(sK2) = iProver_top ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2422,c_39,c_41]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_977,negated_conjecture,
% 11.26/2.01      ( v1_funct_1(sK2) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_30]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1554,plain,
% 11.26/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0)
% 11.26/2.01      | ~ v2_funct_1(X0)
% 11.26/2.01      | ~ v1_relat_1(X0)
% 11.26/2.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_996,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0_49)
% 11.26/2.01      | ~ v2_funct_1(X0_49)
% 11.26/2.01      | ~ v1_relat_1(X0_49)
% 11.26/2.01      | k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_2]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1535,plain,
% 11.26/2.01      ( k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49)
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v2_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v1_relat_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2219,plain,
% 11.26/2.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.26/2.01      | v2_funct_1(sK2) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1554,c_1535]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_991,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.26/2.01      | v1_relat_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_7]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1540,plain,
% 11.26/2.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.26/2.01      | v1_relat_1(X0_49) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1960,plain,
% 11.26/2.01      ( v1_relat_1(sK2) = iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1540]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2280,plain,
% 11.26/2.01      ( v2_funct_1(sK2) != iProver_top
% 11.26/2.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2219,c_1960]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2281,plain,
% 11.26/2.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.26/2.01      | v2_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(renaming,[status(thm)],[c_2280]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2678,plain,
% 11.26/2.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_2673,c_2281]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8336,plain,
% 11.26/2.01      ( k1_relat_1(sK2) = sK0
% 11.26/2.01      | v3_funct_2(k2_funct_1(sK2),X0_50,sK0) != iProver_top
% 11.26/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.26/2.01      inference(demodulation,[status(thm)],[c_8331,c_2678]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8413,plain,
% 11.26/2.01      ( k1_relat_1(sK2) = sK0
% 11.26/2.01      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 11.26/2.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_8336]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8327,plain,
% 11.26/2.01      ( k2_funct_2(sK0,k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 11.26/2.01      | v1_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 11.26/2.01      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_8316,c_1550]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8324,plain,
% 11.26/2.01      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_8316,c_1540]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_8323,plain,
% 11.26/2.01      ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_8316,c_1541]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_5,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0)
% 11.26/2.01      | ~ v2_funct_1(X0)
% 11.26/2.01      | ~ v1_relat_1(X0)
% 11.26/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 11.26/2.01      inference(cnf_transformation,[],[f88]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_993,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0_49)
% 11.26/2.01      | ~ v2_funct_1(X0_49)
% 11.26/2.01      | ~ v1_relat_1(X0_49)
% 11.26/2.01      | k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49)) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_5]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1538,plain,
% 11.26/2.01      ( k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49))
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v2_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v1_relat_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_993]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2373,plain,
% 11.26/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 11.26/2.01      | v2_funct_1(sK2) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1554,c_1538]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2796,plain,
% 11.26/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2373,c_39,c_41,c_1960,c_2422]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0)
% 11.26/2.01      | ~ v1_funct_1(X1)
% 11.26/2.01      | ~ v2_funct_1(X0)
% 11.26/2.01      | ~ v1_relat_1(X0)
% 11.26/2.01      | ~ v1_relat_1(X1)
% 11.26/2.01      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 11.26/2.01      | k1_relat_1(X0) != k2_relat_1(X1)
% 11.26/2.01      | k2_funct_1(X0) = X1 ),
% 11.26/2.01      inference(cnf_transformation,[],[f89]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_992,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0_49)
% 11.26/2.01      | ~ v1_funct_1(X1_49)
% 11.26/2.01      | ~ v2_funct_1(X0_49)
% 11.26/2.01      | ~ v1_relat_1(X0_49)
% 11.26/2.01      | ~ v1_relat_1(X1_49)
% 11.26/2.01      | k1_relat_1(X0_49) != k2_relat_1(X1_49)
% 11.26/2.01      | k5_relat_1(X1_49,X0_49) != k6_partfun1(k2_relat_1(X0_49))
% 11.26/2.01      | k2_funct_1(X0_49) = X1_49 ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_6]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1539,plain,
% 11.26/2.01      ( k1_relat_1(X0_49) != k2_relat_1(X1_49)
% 11.26/2.01      | k5_relat_1(X1_49,X0_49) != k6_partfun1(k2_relat_1(X0_49))
% 11.26/2.01      | k2_funct_1(X0_49) = X1_49
% 11.26/2.01      | v1_funct_1(X1_49) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v2_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v1_relat_1(X0_49) != iProver_top
% 11.26/2.01      | v1_relat_1(X1_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2886,plain,
% 11.26/2.01      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 11.26/2.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
% 11.26/2.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_2796,c_1539]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0)
% 11.26/2.01      | ~ v2_funct_1(X0)
% 11.26/2.01      | ~ v1_relat_1(X0)
% 11.26/2.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_995,plain,
% 11.26/2.01      ( ~ v1_funct_1(X0_49)
% 11.26/2.01      | ~ v2_funct_1(X0_49)
% 11.26/2.01      | ~ v1_relat_1(X0_49)
% 11.26/2.01      | k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_3]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1536,plain,
% 11.26/2.01      ( k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49)
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v2_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v1_relat_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2291,plain,
% 11.26/2.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.26/2.01      | v2_funct_1(sK2) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1554,c_1536]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2577,plain,
% 11.26/2.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2291,c_39,c_41,c_1960,c_2422]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2895,plain,
% 11.26/2.01      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 11.26/2.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
% 11.26/2.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(light_normalisation,[status(thm)],[c_2886,c_2577]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2896,plain,
% 11.26/2.01      ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
% 11.26/2.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.26/2.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(equality_resolution_simp,[status(thm)],[c_2895]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_21,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ v3_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.26/2.01      | ~ v1_funct_1(X0)
% 11.26/2.01      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 11.26/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_984,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49)
% 11.26/2.01      | v1_funct_1(k2_funct_2(X0_50,X0_49)) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_21]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1547,plain,
% 11.26/2.01      ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v1_funct_1(k2_funct_2(X0_50,X0_49)) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2454,plain,
% 11.26/2.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1547]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3338,plain,
% 11.26/2.01      ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2454,c_39,c_40,c_41]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3489,plain,
% 11.26/2.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 11.26/2.01      inference(demodulation,[status(thm)],[c_3486,c_3338]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6407,plain,
% 11.26/2.01      ( v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.26/2.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2)) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2896,c_39,c_1960,c_3489]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6408,plain,
% 11.26/2.01      ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
% 11.26/2.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.26/2.01      inference(renaming,[status(thm)],[c_6407]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6411,plain,
% 11.26/2.01      ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
% 11.26/2.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.26/2.01      inference(light_normalisation,[status(thm)],[c_6408,c_2678]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6412,plain,
% 11.26/2.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.26/2.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.26/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.26/2.01      inference(equality_resolution_simp,[status(thm)],[c_6411]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_31,negated_conjecture,
% 11.26/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.26/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_976,negated_conjecture,
% 11.26/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_31]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1555,plain,
% 11.26/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_976]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_23,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.26/2.01      | ~ v1_funct_1(X0)
% 11.26/2.01      | ~ v1_funct_1(X3)
% 11.26/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_982,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.26/2.01      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49)
% 11.26/2.01      | ~ v1_funct_1(X1_49)
% 11.26/2.01      | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_23]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1549,plain,
% 11.26/2.01      ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.26/2.01      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v1_funct_1(X1_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4021,plain,
% 11.26/2.01      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK2) = k5_relat_1(X0_49,sK2)
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1549]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4318,plain,
% 11.26/2.01      ( v1_funct_1(X0_49) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.26/2.01      | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK2) = k5_relat_1(X0_49,sK2) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_4021,c_39]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4319,plain,
% 11.26/2.01      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK2) = k5_relat_1(X0_49,sK2)
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(renaming,[status(thm)],[c_4318]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4328,plain,
% 11.26/2.01      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 11.26/2.01      | v1_funct_1(sK1) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1555,c_4319]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_10,plain,
% 11.26/2.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.26/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.26/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.26/2.01      | X3 = X2 ),
% 11.26/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_26,negated_conjecture,
% 11.26/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 11.26/2.01      inference(cnf_transformation,[],[f85]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_433,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | X3 = X0
% 11.26/2.01      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 11.26/2.01      | k6_partfun1(sK0) != X3
% 11.26/2.01      | sK0 != X2
% 11.26/2.01      | sK0 != X1 ),
% 11.26/2.01      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_434,plain,
% 11.26/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 11.26/2.01      inference(unflattening,[status(thm)],[c_433]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_22,plain,
% 11.26/2.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.26/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_52,plain,
% 11.26/2.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_22]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_436,plain,
% 11.26/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_434,c_52]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_971,plain,
% 11.26/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_436]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1560,plain,
% 11.26/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 11.26/2.01      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_34,negated_conjecture,
% 11.26/2.01      ( v1_funct_1(sK1) ),
% 11.26/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_16,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.26/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.26/2.01      | ~ v1_funct_1(X0)
% 11.26/2.01      | ~ v1_funct_1(X3) ),
% 11.26/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_989,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.26/2.01      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 11.26/2.01      | m1_subset_1(k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49)
% 11.26/2.01      | ~ v1_funct_1(X1_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_16]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1849,plain,
% 11.26/2.01      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ v1_funct_1(sK1)
% 11.26/2.01      | ~ v1_funct_1(sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_989]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2119,plain,
% 11.26/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_1560,c_34,c_31,c_30,c_27,c_971,c_1849]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4362,plain,
% 11.26/2.01      ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0)
% 11.26/2.01      | v1_funct_1(sK1) != iProver_top ),
% 11.26/2.01      inference(light_normalisation,[status(thm)],[c_4328,c_2119]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2260,plain,
% 11.26/2.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ v1_funct_1(sK1)
% 11.26/2.01      | ~ v1_funct_1(sK2)
% 11.26/2.01      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_982]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2027,plain,
% 11.26/2.01      ( X0_49 != X1_49
% 11.26/2.01      | X0_49 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 11.26/2.01      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X1_49 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1003]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2259,plain,
% 11.26/2.01      ( X0_49 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 11.26/2.01      | X0_49 != k5_relat_1(sK1,sK2)
% 11.26/2.01      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_relat_1(sK1,sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2027]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2645,plain,
% 11.26/2.01      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_relat_1(sK1,sK2)
% 11.26/2.01      | k5_relat_1(sK1,sK2) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 11.26/2.01      | k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2259]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1000,plain,( X0_49 = X0_49 ),theory(equality) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2646,plain,
% 11.26/2.01      ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1915,plain,
% 11.26/2.01      ( X0_49 != X1_49
% 11.26/2.01      | X0_49 = k6_partfun1(X0_50)
% 11.26/2.01      | k6_partfun1(X0_50) != X1_49 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1003]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2101,plain,
% 11.26/2.01      ( X0_49 != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 11.26/2.01      | X0_49 = k6_partfun1(sK0)
% 11.26/2.01      | k6_partfun1(sK0) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1915]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3508,plain,
% 11.26/2.01      ( k5_relat_1(sK1,sK2) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 11.26/2.01      | k5_relat_1(sK1,sK2) = k6_partfun1(sK0)
% 11.26/2.01      | k6_partfun1(sK0) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_2101]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6121,plain,
% 11.26/2.01      ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0) ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_4362,c_34,c_31,c_30,c_27,c_971,c_1849,c_2260,c_2645,
% 11.26/2.01                 c_2646,c_3508]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6124,plain,
% 11.26/2.01      ( k1_relat_1(sK2) != k2_relat_1(sK1)
% 11.26/2.01      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK0)
% 11.26/2.01      | k2_funct_1(sK2) = sK1
% 11.26/2.01      | v1_funct_1(sK1) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top
% 11.26/2.01      | v2_funct_1(sK2) != iProver_top
% 11.26/2.01      | v1_relat_1(sK1) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_6121,c_1539]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4935,plain,
% 11.26/2.01      ( k2_relat_1(sK2) = sK0
% 11.26/2.01      | v3_funct_2(sK2,X0_50,sK0) != iProver_top
% 11.26/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1561]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4997,plain,
% 11.26/2.01      ( k2_relat_1(sK2) = sK0
% 11.26/2.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_4935]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_5316,plain,
% 11.26/2.01      ( k2_relat_1(sK2) = sK0 ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_4935,c_39,c_41,c_42,c_4997]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_4936,plain,
% 11.26/2.01      ( k2_relat_1(sK1) = sK0
% 11.26/2.01      | v3_funct_2(sK1,X0_50,sK0) != iProver_top
% 11.26/2.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
% 11.26/2.01      | v1_funct_1(sK1) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1555,c_1561]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_32,negated_conjecture,
% 11.26/2.01      ( v3_funct_2(sK1,sK0,sK0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1094,plain,
% 11.26/2.01      ( ~ v3_funct_2(sK1,sK0,sK0)
% 11.26/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ v1_funct_1(sK1)
% 11.26/2.01      | k2_relat_1(sK1) = sK0 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_970]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_5397,plain,
% 11.26/2.01      ( k2_relat_1(sK1) = sK0 ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_4936,c_34,c_32,c_31,c_1094]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6125,plain,
% 11.26/2.01      ( k1_relat_1(sK2) != sK0
% 11.26/2.01      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 11.26/2.01      | k2_funct_1(sK2) = sK1
% 11.26/2.01      | v1_funct_1(sK1) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top
% 11.26/2.01      | v2_funct_1(sK2) != iProver_top
% 11.26/2.01      | v1_relat_1(sK1) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(light_normalisation,[status(thm)],[c_6124,c_5316,c_5397]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_6126,plain,
% 11.26/2.01      ( k1_relat_1(sK2) != sK0
% 11.26/2.01      | k2_funct_1(sK2) = sK1
% 11.26/2.01      | v1_funct_1(sK1) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top
% 11.26/2.01      | v2_funct_1(sK2) != iProver_top
% 11.26/2.01      | v1_relat_1(sK1) != iProver_top
% 11.26/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.26/2.01      inference(equality_resolution_simp,[status(thm)],[c_6125]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_20,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0,X1,X1)
% 11.26/2.01      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 11.26/2.01      | ~ v3_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.26/2.01      | ~ v1_funct_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_985,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | v1_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50)
% 11.26/2.01      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_20]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1546,plain,
% 11.26/2.01      ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | v1_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50) = iProver_top
% 11.26/2.01      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3034,plain,
% 11.26/2.01      ( v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 11.26/2.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1546]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3627,plain,
% 11.26/2.01      ( v1_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_3034,c_39,c_40,c_41]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3631,plain,
% 11.26/2.01      ( v1_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
% 11.26/2.01      inference(light_normalisation,[status(thm)],[c_3627,c_3486]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_19,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0,X1,X1)
% 11.26/2.01      | ~ v3_funct_2(X0,X1,X1)
% 11.26/2.01      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 11.26/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.26/2.01      | ~ v1_funct_1(X0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_986,plain,
% 11.26/2.01      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 11.26/2.01      | v3_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50)
% 11.26/2.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 11.26/2.01      | ~ v1_funct_1(X0_49) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_19]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1545,plain,
% 11.26/2.01      ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 11.26/2.01      | v3_funct_2(k2_funct_2(X0_50,X0_49),X0_50,X0_50) = iProver_top
% 11.26/2.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 11.26/2.01      | v1_funct_1(X0_49) != iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_986]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_2996,plain,
% 11.26/2.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 11.26/2.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.26/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.26/2.01      inference(superposition,[status(thm)],[c_1551,c_1545]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3559,plain,
% 11.26/2.01      ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
% 11.26/2.01      inference(global_propositional_subsumption,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_2996,c_39,c_40,c_41]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_3563,plain,
% 11.26/2.01      ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
% 11.26/2.01      inference(light_normalisation,[status(thm)],[c_3559,c_3486]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1868,plain,
% 11.26/2.01      ( sK2 = sK2 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_9,plain,
% 11.26/2.01      ( r2_relset_1(X0,X1,X2,X2)
% 11.26/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 11.26/2.01      inference(cnf_transformation,[],[f90]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_25,negated_conjecture,
% 11.26/2.01      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 11.26/2.01      inference(cnf_transformation,[],[f86]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_423,plain,
% 11.26/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.26/2.01      | k2_funct_2(sK0,sK1) != X0
% 11.26/2.01      | sK2 != X0
% 11.26/2.01      | sK0 != X2
% 11.26/2.01      | sK0 != X1 ),
% 11.26/2.01      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_424,plain,
% 11.26/2.01      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | sK2 != k2_funct_2(sK0,sK1) ),
% 11.26/2.01      inference(unflattening,[status(thm)],[c_423]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_972,plain,
% 11.26/2.01      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | sK2 != k2_funct_2(sK0,sK1) ),
% 11.26/2.01      inference(subtyping,[status(esa)],[c_424]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1065,plain,
% 11.26/2.01      ( ~ v1_funct_2(sK1,sK0,sK0)
% 11.26/2.01      | ~ v3_funct_2(sK1,sK0,sK0)
% 11.26/2.01      | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.26/2.01      | ~ v1_funct_1(sK1) ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_987]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1052,plain,
% 11.26/2.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.26/2.01      | v1_relat_1(X0_49) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1054,plain,
% 11.26/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.26/2.01      | v1_relat_1(sK1) = iProver_top ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1052]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1001,plain,( X0_50 = X0_50 ),theory(equality) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1033,plain,
% 11.26/2.01      ( sK0 = sK0 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1001]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_1032,plain,
% 11.26/2.01      ( sK1 = sK1 ),
% 11.26/2.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_38,plain,
% 11.26/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_33,negated_conjecture,
% 11.26/2.01      ( v1_funct_2(sK1,sK0,sK0) ),
% 11.26/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(c_35,plain,
% 11.26/2.01      ( v1_funct_1(sK1) = iProver_top ),
% 11.26/2.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.26/2.01  
% 11.26/2.01  cnf(contradiction,plain,
% 11.26/2.01      ( $false ),
% 11.26/2.01      inference(minisat,
% 11.26/2.01                [status(thm)],
% 11.26/2.01                [c_54720,c_29143,c_20096,c_17738,c_8834,c_8413,c_8327,
% 11.26/2.01                 c_8324,c_8323,c_6412,c_6126,c_3867,c_3631,c_3563,c_3489,
% 11.26/2.01                 c_2422,c_1960,c_1868,c_972,c_1065,c_1054,c_1033,c_1032,
% 11.26/2.01                 c_42,c_41,c_40,c_39,c_38,c_31,c_32,c_33,c_35,c_34]) ).
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.26/2.01  
% 11.26/2.01  ------                               Statistics
% 11.26/2.01  
% 11.26/2.01  ------ General
% 11.26/2.01  
% 11.26/2.01  abstr_ref_over_cycles:                  0
% 11.26/2.01  abstr_ref_under_cycles:                 0
% 11.26/2.01  gc_basic_clause_elim:                   0
% 11.26/2.01  forced_gc_time:                         0
% 11.26/2.01  parsing_time:                           0.014
% 11.26/2.01  unif_index_cands_time:                  0.
% 11.26/2.01  unif_index_add_time:                    0.
% 11.26/2.01  orderings_time:                         0.
% 11.26/2.01  out_proof_time:                         0.019
% 11.26/2.01  total_time:                             1.406
% 11.26/2.01  num_of_symbols:                         55
% 11.26/2.01  num_of_terms:                           27968
% 11.26/2.01  
% 11.26/2.01  ------ Preprocessing
% 11.26/2.01  
% 11.26/2.01  num_of_splits:                          0
% 11.26/2.01  num_of_split_atoms:                     0
% 11.26/2.01  num_of_reused_defs:                     0
% 11.26/2.01  num_eq_ax_congr_red:                    8
% 11.26/2.01  num_of_sem_filtered_clauses:            1
% 11.26/2.01  num_of_subtypes:                        3
% 11.26/2.01  monotx_restored_types:                  1
% 11.26/2.01  sat_num_of_epr_types:                   0
% 11.26/2.01  sat_num_of_non_cyclic_types:            0
% 11.26/2.01  sat_guarded_non_collapsed_types:        1
% 11.26/2.01  num_pure_diseq_elim:                    0
% 11.26/2.01  simp_replaced_by:                       0
% 11.26/2.01  res_preprocessed:                       161
% 11.26/2.01  prep_upred:                             0
% 11.26/2.01  prep_unflattend:                        17
% 11.26/2.01  smt_new_axioms:                         0
% 11.26/2.01  pred_elim_cands:                        6
% 11.26/2.01  pred_elim:                              3
% 11.26/2.01  pred_elim_cl:                           4
% 11.26/2.01  pred_elim_cycles:                       5
% 11.26/2.01  merged_defs:                            0
% 11.26/2.01  merged_defs_ncl:                        0
% 11.26/2.01  bin_hyper_res:                          0
% 11.26/2.01  prep_cycles:                            4
% 11.26/2.01  pred_elim_time:                         0.009
% 11.26/2.01  splitting_time:                         0.
% 11.26/2.01  sem_filter_time:                        0.
% 11.26/2.01  monotx_time:                            0.001
% 11.26/2.01  subtype_inf_time:                       0.002
% 11.26/2.01  
% 11.26/2.01  ------ Problem properties
% 11.26/2.01  
% 11.26/2.01  clauses:                                30
% 11.26/2.01  conjectures:                            8
% 11.26/2.01  epr:                                    6
% 11.26/2.01  horn:                                   30
% 11.26/2.01  ground:                                 11
% 11.26/2.01  unary:                                  10
% 11.26/2.01  binary:                                 4
% 11.26/2.01  lits:                                   94
% 11.26/2.01  lits_eq:                                14
% 11.26/2.01  fd_pure:                                0
% 11.26/2.01  fd_pseudo:                              0
% 11.26/2.01  fd_cond:                                0
% 11.26/2.01  fd_pseudo_cond:                         2
% 11.26/2.01  ac_symbols:                             0
% 11.26/2.01  
% 11.26/2.01  ------ Propositional Solver
% 11.26/2.01  
% 11.26/2.01  prop_solver_calls:                      34
% 11.26/2.01  prop_fast_solver_calls:                 2988
% 11.26/2.01  smt_solver_calls:                       0
% 11.26/2.01  smt_fast_solver_calls:                  0
% 11.26/2.01  prop_num_of_clauses:                    10431
% 11.26/2.01  prop_preprocess_simplified:             20193
% 11.26/2.01  prop_fo_subsumed:                       478
% 11.26/2.01  prop_solver_time:                       0.
% 11.26/2.01  smt_solver_time:                        0.
% 11.26/2.01  smt_fast_solver_time:                   0.
% 11.26/2.01  prop_fast_solver_time:                  0.
% 11.26/2.01  prop_unsat_core_time:                   0.001
% 11.26/2.01  
% 11.26/2.01  ------ QBF
% 11.26/2.01  
% 11.26/2.01  qbf_q_res:                              0
% 11.26/2.01  qbf_num_tautologies:                    0
% 11.26/2.01  qbf_prep_cycles:                        0
% 11.26/2.01  
% 11.26/2.01  ------ BMC1
% 11.26/2.01  
% 11.26/2.01  bmc1_current_bound:                     -1
% 11.26/2.01  bmc1_last_solved_bound:                 -1
% 11.26/2.01  bmc1_unsat_core_size:                   -1
% 11.26/2.01  bmc1_unsat_core_parents_size:           -1
% 11.26/2.01  bmc1_merge_next_fun:                    0
% 11.26/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.26/2.01  
% 11.26/2.01  ------ Instantiation
% 11.26/2.01  
% 11.26/2.01  inst_num_of_clauses:                    3268
% 11.26/2.01  inst_num_in_passive:                    1650
% 11.26/2.01  inst_num_in_active:                     1597
% 11.26/2.01  inst_num_in_unprocessed:                20
% 11.26/2.01  inst_num_of_loops:                      1742
% 11.26/2.01  inst_num_of_learning_restarts:          0
% 11.26/2.01  inst_num_moves_active_passive:          136
% 11.26/2.01  inst_lit_activity:                      0
% 11.26/2.01  inst_lit_activity_moves:                0
% 11.26/2.01  inst_num_tautologies:                   0
% 11.26/2.01  inst_num_prop_implied:                  0
% 11.26/2.01  inst_num_existing_simplified:           0
% 11.26/2.01  inst_num_eq_res_simplified:             0
% 11.26/2.01  inst_num_child_elim:                    0
% 11.26/2.01  inst_num_of_dismatching_blockings:      5374
% 11.26/2.01  inst_num_of_non_proper_insts:           5181
% 11.26/2.01  inst_num_of_duplicates:                 0
% 11.26/2.01  inst_inst_num_from_inst_to_res:         0
% 11.26/2.01  inst_dismatching_checking_time:         0.
% 11.26/2.01  
% 11.26/2.01  ------ Resolution
% 11.26/2.01  
% 11.26/2.01  res_num_of_clauses:                     0
% 11.26/2.01  res_num_in_passive:                     0
% 11.26/2.01  res_num_in_active:                      0
% 11.26/2.01  res_num_of_loops:                       165
% 11.26/2.01  res_forward_subset_subsumed:            540
% 11.26/2.01  res_backward_subset_subsumed:           8
% 11.26/2.01  res_forward_subsumed:                   0
% 11.26/2.01  res_backward_subsumed:                  0
% 11.26/2.01  res_forward_subsumption_resolution:     2
% 11.26/2.01  res_backward_subsumption_resolution:    0
% 11.26/2.01  res_clause_to_clause_subsumption:       4974
% 11.26/2.01  res_orphan_elimination:                 0
% 11.26/2.01  res_tautology_del:                      675
% 11.26/2.01  res_num_eq_res_simplified:              1
% 11.26/2.01  res_num_sel_changes:                    0
% 11.26/2.01  res_moves_from_active_to_pass:          0
% 11.26/2.01  
% 11.26/2.01  ------ Superposition
% 11.26/2.01  
% 11.26/2.01  sup_time_total:                         0.
% 11.26/2.01  sup_time_generating:                    0.
% 11.26/2.01  sup_time_sim_full:                      0.
% 11.26/2.01  sup_time_sim_immed:                     0.
% 11.26/2.01  
% 11.26/2.01  sup_num_of_clauses:                     1689
% 11.26/2.01  sup_num_in_active:                      323
% 11.26/2.01  sup_num_in_passive:                     1366
% 11.26/2.01  sup_num_of_loops:                       348
% 11.26/2.01  sup_fw_superposition:                   801
% 11.26/2.01  sup_bw_superposition:                   1055
% 11.26/2.01  sup_immediate_simplified:               1183
% 11.26/2.01  sup_given_eliminated:                   0
% 11.26/2.01  comparisons_done:                       0
% 11.26/2.01  comparisons_avoided:                    0
% 11.26/2.01  
% 11.26/2.01  ------ Simplifications
% 11.26/2.01  
% 11.26/2.01  
% 11.26/2.01  sim_fw_subset_subsumed:                 43
% 11.26/2.01  sim_bw_subset_subsumed:                 57
% 11.26/2.01  sim_fw_subsumed:                        38
% 11.26/2.01  sim_bw_subsumed:                        2
% 11.26/2.01  sim_fw_subsumption_res:                 12
% 11.26/2.01  sim_bw_subsumption_res:                 208
% 11.26/2.01  sim_tautology_del:                      6
% 11.26/2.01  sim_eq_tautology_del:                   27
% 11.26/2.01  sim_eq_res_simp:                        5
% 11.26/2.01  sim_fw_demodulated:                     2
% 11.26/2.01  sim_bw_demodulated:                     22
% 11.26/2.01  sim_light_normalised:                   975
% 11.26/2.01  sim_joinable_taut:                      0
% 11.26/2.01  sim_joinable_simp:                      0
% 11.26/2.01  sim_ac_normalised:                      0
% 11.26/2.01  sim_smt_subsumption:                    0
% 11.26/2.01  
%------------------------------------------------------------------------------
