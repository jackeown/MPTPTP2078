%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:51 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 768 expanded)
%              Number of clauses        :   91 ( 233 expanded)
%              Number of leaves         :   21 ( 190 expanded)
%              Depth                    :   21
%              Number of atoms          :  565 (4876 expanded)
%              Number of equality atoms :  214 ( 417 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f45,f44])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f69])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1246,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_478,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_486,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_478,c_17])).

cnf(c_1233,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_4271,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_1233])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4883,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4271,c_33,c_35,c_36,c_38])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1243,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4909,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4883,c_1243])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1242,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1248,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3112,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1242,c_1248])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_490,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_491,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_569,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_491])).

cnf(c_1232,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_2176,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1232])).

cnf(c_2365,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2176,c_33,c_34,c_35,c_36,c_37,c_38])).

cnf(c_3127,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3112,c_2365])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_339,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_340,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_350,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_340,c_12])).

cnf(c_25,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_350,c_25])).

cnf(c_366,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_762,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_366])).

cnf(c_1235,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_3448,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_1235])).

cnf(c_3449,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3448])).

cnf(c_761,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_366])).

cnf(c_1236,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_3447,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_1236])).

cnf(c_3467,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_3447])).

cnf(c_5113,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4909,c_33,c_34,c_35,c_36,c_37,c_38,c_3449,c_3467])).

cnf(c_5114,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5113])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1251,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5119,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5114,c_1251])).

cnf(c_1239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5119,c_1239])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5130,c_3])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2603,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2604,plain,
    ( sK2 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2603])).

cnf(c_2606,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2531,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2532,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2531])).

cnf(c_2534,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_774,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1723,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1724,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1723])).

cnf(c_1726,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_1507,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1508,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1507])).

cnf(c_1510,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_412,plain,
    ( k6_partfun1(X0) != X1
    | k1_relat_1(X1) != k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_413,plain,
    ( k1_relat_1(k6_partfun1(X0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_414,plain,
    ( k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_100,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_86,plain,
    ( k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5138,c_3467,c_3449,c_2606,c_2534,c_1726,c_1510,c_414,c_100,c_86,c_85])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:50:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 30
% 2.97/0.99  conjectures                             6
% 2.97/0.99  EPR                                     6
% 2.97/0.99  Horn                                    28
% 2.97/0.99  unary                                   14
% 2.97/0.99  binary                                  4
% 2.97/0.99  lits                                    83
% 2.97/0.99  lits eq                                 20
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 4
% 2.97/0.99  fd_pseudo_cond                          1
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     none
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       false
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f14,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f32,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.97/0.99    inference(ennf_transformation,[],[f14])).
% 2.97/0.99  
% 2.97/0.99  fof(f33,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.97/0.99    inference(flattening,[],[f32])).
% 2.97/0.99  
% 2.97/0.99  fof(f68,plain,(
% 2.97/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f33])).
% 2.97/0.99  
% 2.97/0.99  fof(f11,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f28,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.97/0.99    inference(ennf_transformation,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(flattening,[],[f28])).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(nnf_transformation,[],[f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f62,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f18,conjecture,(
% 2.97/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f19,negated_conjecture,(
% 2.97/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.97/0.99    inference(negated_conjecture,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.97/0.99    inference(ennf_transformation,[],[f19])).
% 2.97/0.99  
% 2.97/0.99  fof(f39,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.97/0.99    inference(flattening,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f45,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f44,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f46,plain,(
% 2.97/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f45,f44])).
% 2.97/0.99  
% 2.97/0.99  fof(f79,plain,(
% 2.97/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f12,axiom,(
% 2.97/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f64,plain,(
% 2.97/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f15,axiom,(
% 2.97/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f69,plain,(
% 2.97/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f15])).
% 2.97/0.99  
% 2.97/0.99  fof(f85,plain,(
% 2.97/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.97/0.99    inference(definition_unfolding,[],[f64,f69])).
% 2.97/0.99  
% 2.97/0.99  fof(f73,plain,(
% 2.97/0.99    v1_funct_1(sK2)),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f75,plain,(
% 2.97/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f76,plain,(
% 2.97/0.99    v1_funct_1(sK3)),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f78,plain,(
% 2.97/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f17,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f36,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.97/0.99    inference(ennf_transformation,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f37,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.97/0.99    inference(flattening,[],[f36])).
% 2.97/0.99  
% 2.97/0.99  fof(f71,plain,(
% 2.97/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f37])).
% 2.97/0.99  
% 2.97/0.99  fof(f74,plain,(
% 2.97/0.99    v1_funct_2(sK2,sK0,sK1)),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f77,plain,(
% 2.97/0.99    v1_funct_2(sK3,sK1,sK0)),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f10,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f27,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f10])).
% 2.97/0.99  
% 2.97/0.99  fof(f61,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f27])).
% 2.97/0.99  
% 2.97/0.99  fof(f16,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.97/0.99    inference(ennf_transformation,[],[f16])).
% 2.97/0.99  
% 2.97/0.99  fof(f35,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.97/0.99    inference(flattening,[],[f34])).
% 2.97/0.99  
% 2.97/0.99  fof(f70,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f9,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f20,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.97/0.99  
% 2.97/0.99  fof(f26,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f20])).
% 2.97/0.99  
% 2.97/0.99  fof(f60,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f26])).
% 2.97/0.99  
% 2.97/0.99  fof(f13,axiom,(
% 2.97/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f30,plain,(
% 2.97/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.97/0.99    inference(ennf_transformation,[],[f13])).
% 2.97/0.99  
% 2.97/0.99  fof(f31,plain,(
% 2.97/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(flattening,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f43,plain,(
% 2.97/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(nnf_transformation,[],[f31])).
% 2.97/0.99  
% 2.97/0.99  fof(f66,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f43])).
% 2.97/0.99  
% 2.97/0.99  fof(f89,plain,(
% 2.97/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.97/0.99    inference(equality_resolution,[],[f66])).
% 2.97/0.99  
% 2.97/0.99  fof(f8,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f8])).
% 2.97/0.99  
% 2.97/0.99  fof(f59,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f25])).
% 2.97/0.99  
% 2.97/0.99  fof(f80,plain,(
% 2.97/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.97/0.99    inference(cnf_transformation,[],[f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f7,axiom,(
% 2.97/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f58,plain,(
% 2.97/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f7])).
% 2.97/0.99  
% 2.97/0.99  fof(f83,plain,(
% 2.97/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.97/0.99    inference(definition_unfolding,[],[f58,f69])).
% 2.97/0.99  
% 2.97/0.99  fof(f3,axiom,(
% 2.97/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f40,plain,(
% 2.97/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.97/0.99    inference(nnf_transformation,[],[f3])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.97/0.99    inference(flattening,[],[f40])).
% 2.97/0.99  
% 2.97/0.99  fof(f50,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.97/0.99    inference(cnf_transformation,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  fof(f87,plain,(
% 2.97/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.97/0.99    inference(equality_resolution,[],[f50])).
% 2.97/0.99  
% 2.97/0.99  fof(f2,axiom,(
% 2.97/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f21,plain,(
% 2.97/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f2])).
% 2.97/0.99  
% 2.97/0.99  fof(f48,plain,(
% 2.97/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f21])).
% 2.97/0.99  
% 2.97/0.99  fof(f4,axiom,(
% 2.97/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f22,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f4])).
% 2.97/0.99  
% 2.97/0.99  fof(f52,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f22])).
% 2.97/0.99  
% 2.97/0.99  fof(f5,axiom,(
% 2.97/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f5])).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(flattening,[],[f23])).
% 2.97/0.99  
% 2.97/0.99  fof(f53,plain,(
% 2.97/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f57,plain,(
% 2.97/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f7])).
% 2.97/0.99  
% 2.97/0.99  fof(f84,plain,(
% 2.97/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.97/0.99    inference(definition_unfolding,[],[f57,f69])).
% 2.97/0.99  
% 2.97/0.99  fof(f1,axiom,(
% 2.97/0.99    v1_xboole_0(k1_xboole_0)),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f47,plain,(
% 2.97/0.99    v1_xboole_0(k1_xboole_0)),
% 2.97/0.99    inference(cnf_transformation,[],[f1])).
% 2.97/0.99  
% 2.97/0.99  fof(f6,axiom,(
% 2.97/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f55,plain,(
% 2.97/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.97/0.99    inference(cnf_transformation,[],[f6])).
% 2.97/0.99  
% 2.97/0.99  fof(f82,plain,(
% 2.97/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.97/0.99    inference(definition_unfolding,[],[f55,f69])).
% 2.97/0.99  
% 2.97/0.99  cnf(c_20,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.97/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_funct_1(X3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1246,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.97/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.97/0.99      | v1_funct_1(X3) != iProver_top
% 2.97/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_16,plain,
% 2.97/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.97/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.99      | X3 = X2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_26,negated_conjecture,
% 2.97/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_477,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | X3 = X0
% 2.97/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.97/0.99      | k6_partfun1(sK0) != X3
% 2.97/0.99      | sK0 != X2
% 2.97/0.99      | sK0 != X1 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_478,plain,
% 2.97/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.97/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.97/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_17,plain,
% 2.97/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_486,plain,
% 2.97/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.97/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.97/0.99      inference(forward_subsumption_resolution,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_478,c_17]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1233,plain,
% 2.97/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4271,plain,
% 2.97/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.97/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.97/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.97/0.99      | v1_funct_1(sK2) != iProver_top
% 2.97/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1246,c_1233]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_32,negated_conjecture,
% 2.97/0.99      ( v1_funct_1(sK2) ),
% 2.97/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_33,plain,
% 2.97/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_30,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_35,plain,
% 2.97/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_29,negated_conjecture,
% 2.97/0.99      ( v1_funct_1(sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_36,plain,
% 2.97/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_27,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_38,plain,
% 2.97/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4883,plain,
% 2.97/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_4271,c_33,c_35,c_36,c_38]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_24,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.99      | ~ v1_funct_2(X3,X2,X4)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.97/0.99      | ~ v1_funct_1(X3)
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | v2_funct_1(X0)
% 2.97/0.99      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 2.97/0.99      | k1_xboole_0 = X4 ),
% 2.97/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1243,plain,
% 2.97/0.99      ( k1_xboole_0 = X0
% 2.97/0.99      | v1_funct_2(X1,X2,X3) != iProver_top
% 2.97/0.99      | v1_funct_2(X4,X3,X0) != iProver_top
% 2.97/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.97/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.97/0.99      | v1_funct_1(X4) != iProver_top
% 2.97/0.99      | v1_funct_1(X1) != iProver_top
% 2.97/0.99      | v2_funct_1(X1) = iProver_top
% 2.97/0.99      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4909,plain,
% 2.97/0.99      ( sK0 = k1_xboole_0
% 2.97/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.97/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.97/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.97/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.97/0.99      | v1_funct_1(sK2) != iProver_top
% 2.97/0.99      | v1_funct_1(sK3) != iProver_top
% 2.97/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.97/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_4883,c_1243]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_31,negated_conjecture,
% 2.97/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_34,plain,
% 2.97/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_28,negated_conjecture,
% 2.97/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_37,plain,
% 2.97/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1242,plain,
% 2.97/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_14,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1248,plain,
% 2.97/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.97/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3112,plain,
% 2.97/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1242,c_1248]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_22,plain,
% 2.97/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.97/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.97/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/1.00      | ~ v1_funct_1(X2)
% 2.97/1.00      | ~ v1_funct_1(X3)
% 2.97/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_490,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.00      | ~ v1_funct_2(X3,X2,X1)
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | ~ v1_funct_1(X3)
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X2,X1,X3) = X1
% 2.97/1.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 2.97/1.00      | sK0 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_491,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.97/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.97/1.00      | ~ v1_funct_1(X2)
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 2.97/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_569,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.97/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | ~ v1_funct_1(X2)
% 2.97/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.97/1.00      inference(equality_resolution_simp,[status(thm)],[c_491]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1232,plain,
% 2.97/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 2.97/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 2.97/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 2.97/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.97/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.97/1.00      | v1_funct_1(X2) != iProver_top
% 2.97/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2176,plain,
% 2.97/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.97/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.97/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.97/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.97/1.00      | v1_funct_1(sK2) != iProver_top
% 2.97/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.97/1.00      inference(equality_resolution,[status(thm)],[c_1232]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2365,plain,
% 2.97/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_2176,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3127,plain,
% 2.97/1.00      ( k2_relat_1(sK3) = sK0 ),
% 2.97/1.00      inference(light_normalisation,[status(thm)],[c_3112,c_2365]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( v5_relat_1(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_18,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ v1_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_339,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.97/1.00      | ~ v1_relat_1(X0)
% 2.97/1.00      | X0 != X1
% 2.97/1.00      | k2_relat_1(X0) != X3 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_340,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.97/1.00      | ~ v1_relat_1(X0) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_339]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_12,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | v1_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_350,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.97/1.00      inference(forward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_340,c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_25,negated_conjecture,
% 2.97/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_365,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.97/1.00      | ~ v2_funct_1(sK2)
% 2.97/1.00      | k2_relat_1(X0) != sK0
% 2.97/1.00      | sK3 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_350,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_366,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.97/1.00      | ~ v2_funct_1(sK2)
% 2.97/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_762,plain,
% 2.97/1.00      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[])],
% 2.97/1.00                [c_366]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1235,plain,
% 2.97/1.00      ( k2_relat_1(sK3) != sK0
% 2.97/1.00      | v2_funct_1(sK2) != iProver_top
% 2.97/1.00      | sP0_iProver_split = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3448,plain,
% 2.97/1.00      ( sK0 != sK0
% 2.97/1.00      | v2_funct_1(sK2) != iProver_top
% 2.97/1.00      | sP0_iProver_split = iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_3127,c_1235]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3449,plain,
% 2.97/1.00      ( v2_funct_1(sK2) != iProver_top
% 2.97/1.00      | sP0_iProver_split = iProver_top ),
% 2.97/1.00      inference(equality_resolution_simp,[status(thm)],[c_3448]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_761,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.97/1.00      | ~ sP0_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.97/1.00                [c_366]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1236,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 2.97/1.00      | sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3447,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.97/1.00      | sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_3127,c_1236]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3467,plain,
% 2.97/1.00      ( sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1242,c_3447]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5113,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_4909,c_33,c_34,c_35,c_36,c_37,c_38,c_3449,c_3467]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5114,plain,
% 2.97/1.00      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_5113]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_10,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1251,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5119,plain,
% 2.97/1.00      ( sK0 = k1_xboole_0 ),
% 2.97/1.00      inference(forward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_5114,c_1251]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1239,plain,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5130,plain,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_5119,c_1239]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3,plain,
% 2.97/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5138,plain,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_5130,c_3]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1,plain,
% 2.97/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2603,plain,
% 2.97/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2604,plain,
% 2.97/1.00      ( sK2 = X0
% 2.97/1.00      | v1_xboole_0(X0) != iProver_top
% 2.97/1.00      | v1_xboole_0(sK2) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2603]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2606,plain,
% 2.97/1.00      ( sK2 = k1_xboole_0
% 2.97/1.00      | v1_xboole_0(sK2) != iProver_top
% 2.97/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2604]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.00      | ~ v1_xboole_0(X1)
% 2.97/1.00      | v1_xboole_0(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2531,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 2.97/1.00      | ~ v1_xboole_0(X0)
% 2.97/1.00      | v1_xboole_0(sK2) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2532,plain,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 2.97/1.00      | v1_xboole_0(X0) != iProver_top
% 2.97/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2531]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2534,plain,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.97/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.97/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2532]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_774,plain,
% 2.97/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.97/1.00      theory(equality) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1723,plain,
% 2.97/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_774]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1724,plain,
% 2.97/1.00      ( sK2 != X0
% 2.97/1.00      | v2_funct_1(X0) != iProver_top
% 2.97/1.00      | v2_funct_1(sK2) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1723]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1726,plain,
% 2.97/1.00      ( sK2 != k1_xboole_0
% 2.97/1.00      | v2_funct_1(sK2) = iProver_top
% 2.97/1.00      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1724]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1507,plain,
% 2.97/1.00      ( v2_funct_1(X0)
% 2.97/1.00      | ~ v2_funct_1(k6_partfun1(X1))
% 2.97/1.00      | X0 != k6_partfun1(X1) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_774]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1508,plain,
% 2.97/1.00      ( X0 != k6_partfun1(X1)
% 2.97/1.00      | v2_funct_1(X0) = iProver_top
% 2.97/1.00      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1507]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1510,plain,
% 2.97/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 2.97/1.00      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 2.97/1.00      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1508]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_7,plain,
% 2.97/1.00      ( ~ v1_relat_1(X0)
% 2.97/1.00      | k1_relat_1(X0) != k1_xboole_0
% 2.97/1.00      | k1_xboole_0 = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_11,plain,
% 2.97/1.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_412,plain,
% 2.97/1.00      ( k6_partfun1(X0) != X1
% 2.97/1.00      | k1_relat_1(X1) != k1_xboole_0
% 2.97/1.00      | k1_xboole_0 = X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_413,plain,
% 2.97/1.00      ( k1_relat_1(k6_partfun1(X0)) != k1_xboole_0
% 2.97/1.00      | k1_xboole_0 = k6_partfun1(X0) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_414,plain,
% 2.97/1.00      ( k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
% 2.97/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_413]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_0,plain,
% 2.97/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_100,plain,
% 2.97/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_9,plain,
% 2.97/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_86,plain,
% 2.97/1.00      ( k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_83,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_85,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_83]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(contradiction,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(minisat,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_5138,c_3467,c_3449,c_2606,c_2534,c_1726,c_1510,c_414,
% 2.97/1.00                 c_100,c_86,c_85]) ).
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  ------                               Statistics
% 2.97/1.00  
% 2.97/1.00  ------ General
% 2.97/1.00  
% 2.97/1.00  abstr_ref_over_cycles:                  0
% 2.97/1.00  abstr_ref_under_cycles:                 0
% 2.97/1.00  gc_basic_clause_elim:                   0
% 2.97/1.00  forced_gc_time:                         0
% 2.97/1.00  parsing_time:                           0.012
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.01
% 2.97/1.00  total_time:                             0.22
% 2.97/1.00  num_of_symbols:                         53
% 2.97/1.00  num_of_terms:                           5534
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing
% 2.97/1.00  
% 2.97/1.00  num_of_splits:                          1
% 2.97/1.00  num_of_split_atoms:                     1
% 2.97/1.00  num_of_reused_defs:                     0
% 2.97/1.00  num_eq_ax_congr_red:                    8
% 2.97/1.00  num_of_sem_filtered_clauses:            1
% 2.97/1.00  num_of_subtypes:                        0
% 2.97/1.00  monotx_restored_types:                  0
% 2.97/1.00  sat_num_of_epr_types:                   0
% 2.97/1.00  sat_num_of_non_cyclic_types:            0
% 2.97/1.00  sat_guarded_non_collapsed_types:        0
% 2.97/1.00  num_pure_diseq_elim:                    0
% 2.97/1.00  simp_replaced_by:                       0
% 2.97/1.00  res_preprocessed:                       153
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        21
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        6
% 2.97/1.00  pred_elim:                              3
% 2.97/1.00  pred_elim_cl:                           4
% 2.97/1.00  pred_elim_cycles:                       6
% 2.97/1.00  merged_defs:                            0
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          0
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.007
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.
% 2.97/1.00  subtype_inf_time:                       0.
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                30
% 2.97/1.00  conjectures:                            6
% 2.97/1.00  epr:                                    6
% 2.97/1.00  horn:                                   28
% 2.97/1.00  ground:                                 9
% 2.97/1.00  unary:                                  14
% 2.97/1.00  binary:                                 4
% 2.97/1.00  lits:                                   83
% 2.97/1.00  lits_eq:                                20
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                4
% 2.97/1.00  fd_pseudo_cond:                         1
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      26
% 2.97/1.00  prop_fast_solver_calls:                 1086
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    1936
% 2.97/1.00  prop_preprocess_simplified:             6557
% 2.97/1.00  prop_fo_subsumed:                       25
% 2.97/1.00  prop_solver_time:                       0.
% 2.97/1.00  smt_solver_time:                        0.
% 2.97/1.00  smt_fast_solver_time:                   0.
% 2.97/1.00  prop_fast_solver_time:                  0.
% 2.97/1.00  prop_unsat_core_time:                   0.
% 2.97/1.00  
% 2.97/1.00  ------ QBF
% 2.97/1.00  
% 2.97/1.00  qbf_q_res:                              0
% 2.97/1.00  qbf_num_tautologies:                    0
% 2.97/1.00  qbf_prep_cycles:                        0
% 2.97/1.00  
% 2.97/1.00  ------ BMC1
% 2.97/1.00  
% 2.97/1.00  bmc1_current_bound:                     -1
% 2.97/1.00  bmc1_last_solved_bound:                 -1
% 2.97/1.00  bmc1_unsat_core_size:                   -1
% 2.97/1.00  bmc1_unsat_core_parents_size:           -1
% 2.97/1.00  bmc1_merge_next_fun:                    0
% 2.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation
% 2.97/1.00  
% 2.97/1.00  inst_num_of_clauses:                    689
% 2.97/1.00  inst_num_in_passive:                    77
% 2.97/1.00  inst_num_in_active:                     325
% 2.97/1.00  inst_num_in_unprocessed:                287
% 2.97/1.00  inst_num_of_loops:                      330
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          4
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                0
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      47
% 2.97/1.00  inst_num_of_non_proper_insts:           520
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       157
% 2.97/1.00  res_forward_subset_subsumed:            16
% 2.97/1.00  res_backward_subset_subsumed:           0
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     4
% 2.97/1.00  res_backward_subsumption_resolution:    0
% 2.97/1.00  res_clause_to_clause_subsumption:       149
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      30
% 2.97/1.00  res_num_eq_res_simplified:              1
% 2.97/1.00  res_num_sel_changes:                    0
% 2.97/1.00  res_moves_from_active_to_pass:          0
% 2.97/1.00  
% 2.97/1.00  ------ Superposition
% 2.97/1.00  
% 2.97/1.00  sup_time_total:                         0.
% 2.97/1.00  sup_time_generating:                    0.
% 2.97/1.00  sup_time_sim_full:                      0.
% 2.97/1.00  sup_time_sim_immed:                     0.
% 2.97/1.00  
% 2.97/1.00  sup_num_of_clauses:                     62
% 2.97/1.00  sup_num_in_active:                      45
% 2.97/1.00  sup_num_in_passive:                     17
% 2.97/1.00  sup_num_of_loops:                       65
% 2.97/1.00  sup_fw_superposition:                   30
% 2.97/1.00  sup_bw_superposition:                   30
% 2.97/1.00  sup_immediate_simplified:               22
% 2.97/1.00  sup_given_eliminated:                   1
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    0
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 1
% 2.97/1.00  sim_bw_subset_subsumed:                 0
% 2.97/1.00  sim_fw_subsumed:                        4
% 2.97/1.00  sim_bw_subsumed:                        1
% 2.97/1.00  sim_fw_subsumption_res:                 1
% 2.97/1.00  sim_bw_subsumption_res:                 0
% 2.97/1.00  sim_tautology_del:                      3
% 2.97/1.00  sim_eq_tautology_del:                   4
% 2.97/1.00  sim_eq_res_simp:                        2
% 2.97/1.00  sim_fw_demodulated:                     9
% 2.97/1.00  sim_bw_demodulated:                     23
% 2.97/1.00  sim_light_normalised:                   10
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
