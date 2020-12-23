%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:18 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 790 expanded)
%              Number of clauses        :  100 ( 247 expanded)
%              Number of leaves         :   24 ( 196 expanded)
%              Depth                    :   21
%              Number of atoms          :  584 (5018 expanded)
%              Number of equality atoms :  225 ( 477 expanded)
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

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
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
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f45,f44])).

fof(f77,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f78,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f67])).

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

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f38])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f67])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1098,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_458,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_466,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_458,c_15])).

cnf(c_1084,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_2916,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1084])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2983,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2916,c_31,c_33,c_34,c_36])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1095,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3010,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_1095])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1796,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_1797,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1796])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1881,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1882,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_1094,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1100,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2108,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1094,c_1100])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_471,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_471])).

cnf(c_1083,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_1852,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1083])).

cnf(c_1891,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1852,c_31,c_32,c_33,c_34,c_35,c_36])).

cnf(c_2123,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2108,c_1891])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_23,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_376,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_377,plain,
    ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != X2
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_377])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_672,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_398])).

cnf(c_1086,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_2170,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2123,c_1086])).

cnf(c_2176,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2170])).

cnf(c_671,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_398])).

cnf(c_1087,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_2171,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2123,c_1087])).

cnf(c_2190,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_2171])).

cnf(c_6387,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3010,c_31,c_32,c_33,c_34,c_35,c_36,c_1797,c_1882,c_2176,c_2190])).

cnf(c_6388,plain,
    ( sK1 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6387])).

cnf(c_9,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1102,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6393,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6388,c_1102])).

cnf(c_1091,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6427,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6393,c_1091])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6435,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6427,c_3])).

cnf(c_675,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1773,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_2285,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_2286,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_681,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1973,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1974,plain,
    ( sK3 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_1976,plain,
    ( sK3 != k1_xboole_0
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_1607,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1608,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_674,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1498,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_306])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_1462,plain,
    ( k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_1333,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1334,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_1336,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_78,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_80,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6435,c_2286,c_2190,c_2176,c_1976,c_1882,c_1797,c_1608,c_1498,c_1462,c_1336,c_89,c_88,c_8,c_80,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.29/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.99  
% 3.29/0.99  ------  iProver source info
% 3.29/0.99  
% 3.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.99  git: non_committed_changes: false
% 3.29/0.99  git: last_make_outside_of_git: false
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  
% 3.29/0.99  ------ Input Options
% 3.29/0.99  
% 3.29/0.99  --out_options                           all
% 3.29/0.99  --tptp_safe_out                         true
% 3.29/0.99  --problem_path                          ""
% 3.29/0.99  --include_path                          ""
% 3.29/0.99  --clausifier                            res/vclausify_rel
% 3.29/0.99  --clausifier_options                    --mode clausify
% 3.29/0.99  --stdin                                 false
% 3.29/0.99  --stats_out                             all
% 3.29/0.99  
% 3.29/0.99  ------ General Options
% 3.29/0.99  
% 3.29/0.99  --fof                                   false
% 3.29/0.99  --time_out_real                         305.
% 3.29/0.99  --time_out_virtual                      -1.
% 3.29/0.99  --symbol_type_check                     false
% 3.29/0.99  --clausify_out                          false
% 3.29/0.99  --sig_cnt_out                           false
% 3.29/0.99  --trig_cnt_out                          false
% 3.29/0.99  --trig_cnt_out_tolerance                1.
% 3.29/0.99  --trig_cnt_out_sk_spl                   false
% 3.29/0.99  --abstr_cl_out                          false
% 3.29/0.99  
% 3.29/0.99  ------ Global Options
% 3.29/0.99  
% 3.29/0.99  --schedule                              default
% 3.29/0.99  --add_important_lit                     false
% 3.29/0.99  --prop_solver_per_cl                    1000
% 3.29/0.99  --min_unsat_core                        false
% 3.29/0.99  --soft_assumptions                      false
% 3.29/0.99  --soft_lemma_size                       3
% 3.29/0.99  --prop_impl_unit_size                   0
% 3.29/0.99  --prop_impl_unit                        []
% 3.29/0.99  --share_sel_clauses                     true
% 3.29/0.99  --reset_solvers                         false
% 3.29/0.99  --bc_imp_inh                            [conj_cone]
% 3.29/0.99  --conj_cone_tolerance                   3.
% 3.29/0.99  --extra_neg_conj                        none
% 3.29/0.99  --large_theory_mode                     true
% 3.29/0.99  --prolific_symb_bound                   200
% 3.29/0.99  --lt_threshold                          2000
% 3.29/0.99  --clause_weak_htbl                      true
% 3.29/0.99  --gc_record_bc_elim                     false
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing Options
% 3.29/0.99  
% 3.29/0.99  --preprocessing_flag                    true
% 3.29/0.99  --time_out_prep_mult                    0.1
% 3.29/0.99  --splitting_mode                        input
% 3.29/0.99  --splitting_grd                         true
% 3.29/0.99  --splitting_cvd                         false
% 3.29/0.99  --splitting_cvd_svl                     false
% 3.29/0.99  --splitting_nvd                         32
% 3.29/0.99  --sub_typing                            true
% 3.29/0.99  --prep_gs_sim                           true
% 3.29/0.99  --prep_unflatten                        true
% 3.29/0.99  --prep_res_sim                          true
% 3.29/0.99  --prep_upred                            true
% 3.29/0.99  --prep_sem_filter                       exhaustive
% 3.29/0.99  --prep_sem_filter_out                   false
% 3.29/0.99  --pred_elim                             true
% 3.29/0.99  --res_sim_input                         true
% 3.29/0.99  --eq_ax_congr_red                       true
% 3.29/0.99  --pure_diseq_elim                       true
% 3.29/0.99  --brand_transform                       false
% 3.29/0.99  --non_eq_to_eq                          false
% 3.29/0.99  --prep_def_merge                        true
% 3.29/0.99  --prep_def_merge_prop_impl              false
% 3.29/0.99  --prep_def_merge_mbd                    true
% 3.29/0.99  --prep_def_merge_tr_red                 false
% 3.29/0.99  --prep_def_merge_tr_cl                  false
% 3.29/0.99  --smt_preprocessing                     true
% 3.29/0.99  --smt_ac_axioms                         fast
% 3.29/0.99  --preprocessed_out                      false
% 3.29/0.99  --preprocessed_stats                    false
% 3.29/0.99  
% 3.29/0.99  ------ Abstraction refinement Options
% 3.29/0.99  
% 3.29/0.99  --abstr_ref                             []
% 3.29/0.99  --abstr_ref_prep                        false
% 3.29/0.99  --abstr_ref_until_sat                   false
% 3.29/0.99  --abstr_ref_sig_restrict                funpre
% 3.29/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.99  --abstr_ref_under                       []
% 3.29/0.99  
% 3.29/0.99  ------ SAT Options
% 3.29/0.99  
% 3.29/0.99  --sat_mode                              false
% 3.29/0.99  --sat_fm_restart_options                ""
% 3.29/0.99  --sat_gr_def                            false
% 3.29/0.99  --sat_epr_types                         true
% 3.29/0.99  --sat_non_cyclic_types                  false
% 3.29/0.99  --sat_finite_models                     false
% 3.29/0.99  --sat_fm_lemmas                         false
% 3.29/0.99  --sat_fm_prep                           false
% 3.29/0.99  --sat_fm_uc_incr                        true
% 3.29/0.99  --sat_out_model                         small
% 3.29/0.99  --sat_out_clauses                       false
% 3.29/0.99  
% 3.29/0.99  ------ QBF Options
% 3.29/0.99  
% 3.29/0.99  --qbf_mode                              false
% 3.29/0.99  --qbf_elim_univ                         false
% 3.29/0.99  --qbf_dom_inst                          none
% 3.29/0.99  --qbf_dom_pre_inst                      false
% 3.29/0.99  --qbf_sk_in                             false
% 3.29/0.99  --qbf_pred_elim                         true
% 3.29/0.99  --qbf_split                             512
% 3.29/0.99  
% 3.29/0.99  ------ BMC1 Options
% 3.29/0.99  
% 3.29/0.99  --bmc1_incremental                      false
% 3.29/0.99  --bmc1_axioms                           reachable_all
% 3.29/0.99  --bmc1_min_bound                        0
% 3.29/0.99  --bmc1_max_bound                        -1
% 3.29/0.99  --bmc1_max_bound_default                -1
% 3.29/0.99  --bmc1_symbol_reachability              true
% 3.29/0.99  --bmc1_property_lemmas                  false
% 3.29/0.99  --bmc1_k_induction                      false
% 3.29/0.99  --bmc1_non_equiv_states                 false
% 3.29/0.99  --bmc1_deadlock                         false
% 3.29/0.99  --bmc1_ucm                              false
% 3.29/0.99  --bmc1_add_unsat_core                   none
% 3.29/0.99  --bmc1_unsat_core_children              false
% 3.29/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.99  --bmc1_out_stat                         full
% 3.29/0.99  --bmc1_ground_init                      false
% 3.29/0.99  --bmc1_pre_inst_next_state              false
% 3.29/0.99  --bmc1_pre_inst_state                   false
% 3.29/0.99  --bmc1_pre_inst_reach_state             false
% 3.29/0.99  --bmc1_out_unsat_core                   false
% 3.29/0.99  --bmc1_aig_witness_out                  false
% 3.29/0.99  --bmc1_verbose                          false
% 3.29/0.99  --bmc1_dump_clauses_tptp                false
% 3.29/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.99  --bmc1_dump_file                        -
% 3.29/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.99  --bmc1_ucm_extend_mode                  1
% 3.29/0.99  --bmc1_ucm_init_mode                    2
% 3.29/0.99  --bmc1_ucm_cone_mode                    none
% 3.29/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.99  --bmc1_ucm_relax_model                  4
% 3.29/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.99  --bmc1_ucm_layered_model                none
% 3.29/0.99  --bmc1_ucm_max_lemma_size               10
% 3.29/0.99  
% 3.29/0.99  ------ AIG Options
% 3.29/0.99  
% 3.29/0.99  --aig_mode                              false
% 3.29/0.99  
% 3.29/0.99  ------ Instantiation Options
% 3.29/0.99  
% 3.29/0.99  --instantiation_flag                    true
% 3.29/0.99  --inst_sos_flag                         false
% 3.29/0.99  --inst_sos_phase                        true
% 3.29/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.99  --inst_lit_sel_side                     num_symb
% 3.29/0.99  --inst_solver_per_active                1400
% 3.29/0.99  --inst_solver_calls_frac                1.
% 3.29/0.99  --inst_passive_queue_type               priority_queues
% 3.29/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.99  --inst_passive_queues_freq              [25;2]
% 3.29/0.99  --inst_dismatching                      true
% 3.29/0.99  --inst_eager_unprocessed_to_passive     true
% 3.29/0.99  --inst_prop_sim_given                   true
% 3.29/0.99  --inst_prop_sim_new                     false
% 3.29/0.99  --inst_subs_new                         false
% 3.29/0.99  --inst_eq_res_simp                      false
% 3.29/0.99  --inst_subs_given                       false
% 3.29/0.99  --inst_orphan_elimination               true
% 3.29/0.99  --inst_learning_loop_flag               true
% 3.29/0.99  --inst_learning_start                   3000
% 3.29/0.99  --inst_learning_factor                  2
% 3.29/0.99  --inst_start_prop_sim_after_learn       3
% 3.29/0.99  --inst_sel_renew                        solver
% 3.29/0.99  --inst_lit_activity_flag                true
% 3.29/0.99  --inst_restr_to_given                   false
% 3.29/0.99  --inst_activity_threshold               500
% 3.29/0.99  --inst_out_proof                        true
% 3.29/0.99  
% 3.29/0.99  ------ Resolution Options
% 3.29/0.99  
% 3.29/0.99  --resolution_flag                       true
% 3.29/0.99  --res_lit_sel                           adaptive
% 3.29/0.99  --res_lit_sel_side                      none
% 3.29/0.99  --res_ordering                          kbo
% 3.29/0.99  --res_to_prop_solver                    active
% 3.29/0.99  --res_prop_simpl_new                    false
% 3.29/0.99  --res_prop_simpl_given                  true
% 3.29/0.99  --res_passive_queue_type                priority_queues
% 3.29/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.99  --res_passive_queues_freq               [15;5]
% 3.29/0.99  --res_forward_subs                      full
% 3.29/0.99  --res_backward_subs                     full
% 3.29/0.99  --res_forward_subs_resolution           true
% 3.29/0.99  --res_backward_subs_resolution          true
% 3.29/0.99  --res_orphan_elimination                true
% 3.29/0.99  --res_time_limit                        2.
% 3.29/0.99  --res_out_proof                         true
% 3.29/0.99  
% 3.29/0.99  ------ Superposition Options
% 3.29/0.99  
% 3.29/0.99  --superposition_flag                    true
% 3.29/0.99  --sup_passive_queue_type                priority_queues
% 3.29/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.99  --demod_completeness_check              fast
% 3.29/0.99  --demod_use_ground                      true
% 3.29/0.99  --sup_to_prop_solver                    passive
% 3.29/0.99  --sup_prop_simpl_new                    true
% 3.29/0.99  --sup_prop_simpl_given                  true
% 3.29/0.99  --sup_fun_splitting                     false
% 3.29/0.99  --sup_smt_interval                      50000
% 3.29/0.99  
% 3.29/0.99  ------ Superposition Simplification Setup
% 3.29/0.99  
% 3.29/0.99  --sup_indices_passive                   []
% 3.29/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.99  --sup_full_bw                           [BwDemod]
% 3.29/0.99  --sup_immed_triv                        [TrivRules]
% 3.29/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.99  --sup_immed_bw_main                     []
% 3.29/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.99  
% 3.29/0.99  ------ Combination Options
% 3.29/0.99  
% 3.29/0.99  --comb_res_mult                         3
% 3.29/0.99  --comb_sup_mult                         2
% 3.29/0.99  --comb_inst_mult                        10
% 3.29/0.99  
% 3.29/0.99  ------ Debug Options
% 3.29/0.99  
% 3.29/0.99  --dbg_backtrace                         false
% 3.29/0.99  --dbg_dump_prop_clauses                 false
% 3.29/0.99  --dbg_dump_prop_clauses_file            -
% 3.29/0.99  --dbg_out_stat                          false
% 3.29/0.99  ------ Parsing...
% 3.29/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.99  ------ Proving...
% 3.29/0.99  ------ Problem Properties 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  clauses                                 26
% 3.29/0.99  conjectures                             6
% 3.29/0.99  EPR                                     4
% 3.29/0.99  Horn                                    24
% 3.29/0.99  unary                                   13
% 3.29/0.99  binary                                  4
% 3.29/0.99  lits                                    74
% 3.29/0.99  lits eq                                 15
% 3.29/0.99  fd_pure                                 0
% 3.29/0.99  fd_pseudo                               0
% 3.29/0.99  fd_cond                                 3
% 3.29/0.99  fd_pseudo_cond                          0
% 3.29/0.99  AC symbols                              0
% 3.29/0.99  
% 3.29/0.99  ------ Schedule dynamic 5 is on 
% 3.29/0.99  
% 3.29/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  Current options:
% 3.29/0.99  ------ 
% 3.29/0.99  
% 3.29/0.99  ------ Input Options
% 3.29/0.99  
% 3.29/0.99  --out_options                           all
% 3.29/0.99  --tptp_safe_out                         true
% 3.29/0.99  --problem_path                          ""
% 3.29/0.99  --include_path                          ""
% 3.29/0.99  --clausifier                            res/vclausify_rel
% 3.29/0.99  --clausifier_options                    --mode clausify
% 3.29/0.99  --stdin                                 false
% 3.29/0.99  --stats_out                             all
% 3.29/0.99  
% 3.29/0.99  ------ General Options
% 3.29/0.99  
% 3.29/0.99  --fof                                   false
% 3.29/0.99  --time_out_real                         305.
% 3.29/0.99  --time_out_virtual                      -1.
% 3.29/0.99  --symbol_type_check                     false
% 3.29/0.99  --clausify_out                          false
% 3.29/0.99  --sig_cnt_out                           false
% 3.29/0.99  --trig_cnt_out                          false
% 3.29/0.99  --trig_cnt_out_tolerance                1.
% 3.29/0.99  --trig_cnt_out_sk_spl                   false
% 3.29/0.99  --abstr_cl_out                          false
% 3.29/0.99  
% 3.29/0.99  ------ Global Options
% 3.29/0.99  
% 3.29/0.99  --schedule                              default
% 3.29/0.99  --add_important_lit                     false
% 3.29/0.99  --prop_solver_per_cl                    1000
% 3.29/0.99  --min_unsat_core                        false
% 3.29/0.99  --soft_assumptions                      false
% 3.29/0.99  --soft_lemma_size                       3
% 3.29/0.99  --prop_impl_unit_size                   0
% 3.29/0.99  --prop_impl_unit                        []
% 3.29/0.99  --share_sel_clauses                     true
% 3.29/0.99  --reset_solvers                         false
% 3.29/0.99  --bc_imp_inh                            [conj_cone]
% 3.29/0.99  --conj_cone_tolerance                   3.
% 3.29/0.99  --extra_neg_conj                        none
% 3.29/0.99  --large_theory_mode                     true
% 3.29/0.99  --prolific_symb_bound                   200
% 3.29/0.99  --lt_threshold                          2000
% 3.29/0.99  --clause_weak_htbl                      true
% 3.29/0.99  --gc_record_bc_elim                     false
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing Options
% 3.29/0.99  
% 3.29/0.99  --preprocessing_flag                    true
% 3.29/0.99  --time_out_prep_mult                    0.1
% 3.29/0.99  --splitting_mode                        input
% 3.29/0.99  --splitting_grd                         true
% 3.29/0.99  --splitting_cvd                         false
% 3.29/0.99  --splitting_cvd_svl                     false
% 3.29/0.99  --splitting_nvd                         32
% 3.29/0.99  --sub_typing                            true
% 3.29/0.99  --prep_gs_sim                           true
% 3.29/0.99  --prep_unflatten                        true
% 3.29/0.99  --prep_res_sim                          true
% 3.29/0.99  --prep_upred                            true
% 3.29/0.99  --prep_sem_filter                       exhaustive
% 3.29/0.99  --prep_sem_filter_out                   false
% 3.29/0.99  --pred_elim                             true
% 3.29/0.99  --res_sim_input                         true
% 3.29/0.99  --eq_ax_congr_red                       true
% 3.29/0.99  --pure_diseq_elim                       true
% 3.29/0.99  --brand_transform                       false
% 3.29/0.99  --non_eq_to_eq                          false
% 3.29/0.99  --prep_def_merge                        true
% 3.29/0.99  --prep_def_merge_prop_impl              false
% 3.29/0.99  --prep_def_merge_mbd                    true
% 3.29/0.99  --prep_def_merge_tr_red                 false
% 3.29/0.99  --prep_def_merge_tr_cl                  false
% 3.29/0.99  --smt_preprocessing                     true
% 3.29/0.99  --smt_ac_axioms                         fast
% 3.29/0.99  --preprocessed_out                      false
% 3.29/0.99  --preprocessed_stats                    false
% 3.29/0.99  
% 3.29/0.99  ------ Abstraction refinement Options
% 3.29/0.99  
% 3.29/0.99  --abstr_ref                             []
% 3.29/0.99  --abstr_ref_prep                        false
% 3.29/0.99  --abstr_ref_until_sat                   false
% 3.29/0.99  --abstr_ref_sig_restrict                funpre
% 3.29/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.99  --abstr_ref_under                       []
% 3.29/0.99  
% 3.29/0.99  ------ SAT Options
% 3.29/0.99  
% 3.29/0.99  --sat_mode                              false
% 3.29/0.99  --sat_fm_restart_options                ""
% 3.29/0.99  --sat_gr_def                            false
% 3.29/0.99  --sat_epr_types                         true
% 3.29/0.99  --sat_non_cyclic_types                  false
% 3.29/0.99  --sat_finite_models                     false
% 3.29/0.99  --sat_fm_lemmas                         false
% 3.29/0.99  --sat_fm_prep                           false
% 3.29/0.99  --sat_fm_uc_incr                        true
% 3.29/0.99  --sat_out_model                         small
% 3.29/0.99  --sat_out_clauses                       false
% 3.29/0.99  
% 3.29/0.99  ------ QBF Options
% 3.29/0.99  
% 3.29/0.99  --qbf_mode                              false
% 3.29/0.99  --qbf_elim_univ                         false
% 3.29/0.99  --qbf_dom_inst                          none
% 3.29/0.99  --qbf_dom_pre_inst                      false
% 3.29/0.99  --qbf_sk_in                             false
% 3.29/0.99  --qbf_pred_elim                         true
% 3.29/0.99  --qbf_split                             512
% 3.29/0.99  
% 3.29/0.99  ------ BMC1 Options
% 3.29/0.99  
% 3.29/0.99  --bmc1_incremental                      false
% 3.29/0.99  --bmc1_axioms                           reachable_all
% 3.29/0.99  --bmc1_min_bound                        0
% 3.29/0.99  --bmc1_max_bound                        -1
% 3.29/0.99  --bmc1_max_bound_default                -1
% 3.29/0.99  --bmc1_symbol_reachability              true
% 3.29/0.99  --bmc1_property_lemmas                  false
% 3.29/0.99  --bmc1_k_induction                      false
% 3.29/0.99  --bmc1_non_equiv_states                 false
% 3.29/0.99  --bmc1_deadlock                         false
% 3.29/0.99  --bmc1_ucm                              false
% 3.29/0.99  --bmc1_add_unsat_core                   none
% 3.29/0.99  --bmc1_unsat_core_children              false
% 3.29/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.99  --bmc1_out_stat                         full
% 3.29/0.99  --bmc1_ground_init                      false
% 3.29/0.99  --bmc1_pre_inst_next_state              false
% 3.29/0.99  --bmc1_pre_inst_state                   false
% 3.29/0.99  --bmc1_pre_inst_reach_state             false
% 3.29/0.99  --bmc1_out_unsat_core                   false
% 3.29/0.99  --bmc1_aig_witness_out                  false
% 3.29/0.99  --bmc1_verbose                          false
% 3.29/0.99  --bmc1_dump_clauses_tptp                false
% 3.29/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.99  --bmc1_dump_file                        -
% 3.29/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.99  --bmc1_ucm_extend_mode                  1
% 3.29/0.99  --bmc1_ucm_init_mode                    2
% 3.29/0.99  --bmc1_ucm_cone_mode                    none
% 3.29/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.99  --bmc1_ucm_relax_model                  4
% 3.29/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.99  --bmc1_ucm_layered_model                none
% 3.29/0.99  --bmc1_ucm_max_lemma_size               10
% 3.29/0.99  
% 3.29/0.99  ------ AIG Options
% 3.29/0.99  
% 3.29/0.99  --aig_mode                              false
% 3.29/0.99  
% 3.29/0.99  ------ Instantiation Options
% 3.29/0.99  
% 3.29/0.99  --instantiation_flag                    true
% 3.29/0.99  --inst_sos_flag                         false
% 3.29/0.99  --inst_sos_phase                        true
% 3.29/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.99  --inst_lit_sel_side                     none
% 3.29/0.99  --inst_solver_per_active                1400
% 3.29/0.99  --inst_solver_calls_frac                1.
% 3.29/0.99  --inst_passive_queue_type               priority_queues
% 3.29/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.99  --inst_passive_queues_freq              [25;2]
% 3.29/0.99  --inst_dismatching                      true
% 3.29/0.99  --inst_eager_unprocessed_to_passive     true
% 3.29/0.99  --inst_prop_sim_given                   true
% 3.29/0.99  --inst_prop_sim_new                     false
% 3.29/0.99  --inst_subs_new                         false
% 3.29/0.99  --inst_eq_res_simp                      false
% 3.29/0.99  --inst_subs_given                       false
% 3.29/0.99  --inst_orphan_elimination               true
% 3.29/0.99  --inst_learning_loop_flag               true
% 3.29/0.99  --inst_learning_start                   3000
% 3.29/0.99  --inst_learning_factor                  2
% 3.29/0.99  --inst_start_prop_sim_after_learn       3
% 3.29/0.99  --inst_sel_renew                        solver
% 3.29/0.99  --inst_lit_activity_flag                true
% 3.29/0.99  --inst_restr_to_given                   false
% 3.29/0.99  --inst_activity_threshold               500
% 3.29/0.99  --inst_out_proof                        true
% 3.29/0.99  
% 3.29/0.99  ------ Resolution Options
% 3.29/0.99  
% 3.29/0.99  --resolution_flag                       false
% 3.29/0.99  --res_lit_sel                           adaptive
% 3.29/0.99  --res_lit_sel_side                      none
% 3.29/0.99  --res_ordering                          kbo
% 3.29/0.99  --res_to_prop_solver                    active
% 3.29/0.99  --res_prop_simpl_new                    false
% 3.29/0.99  --res_prop_simpl_given                  true
% 3.29/0.99  --res_passive_queue_type                priority_queues
% 3.29/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.99  --res_passive_queues_freq               [15;5]
% 3.29/0.99  --res_forward_subs                      full
% 3.29/0.99  --res_backward_subs                     full
% 3.29/0.99  --res_forward_subs_resolution           true
% 3.29/0.99  --res_backward_subs_resolution          true
% 3.29/0.99  --res_orphan_elimination                true
% 3.29/0.99  --res_time_limit                        2.
% 3.29/0.99  --res_out_proof                         true
% 3.29/0.99  
% 3.29/0.99  ------ Superposition Options
% 3.29/0.99  
% 3.29/0.99  --superposition_flag                    true
% 3.29/0.99  --sup_passive_queue_type                priority_queues
% 3.29/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.99  --demod_completeness_check              fast
% 3.29/0.99  --demod_use_ground                      true
% 3.29/0.99  --sup_to_prop_solver                    passive
% 3.29/0.99  --sup_prop_simpl_new                    true
% 3.29/0.99  --sup_prop_simpl_given                  true
% 3.29/0.99  --sup_fun_splitting                     false
% 3.29/0.99  --sup_smt_interval                      50000
% 3.29/0.99  
% 3.29/0.99  ------ Superposition Simplification Setup
% 3.29/0.99  
% 3.29/0.99  --sup_indices_passive                   []
% 3.29/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.99  --sup_full_bw                           [BwDemod]
% 3.29/0.99  --sup_immed_triv                        [TrivRules]
% 3.29/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.99  --sup_immed_bw_main                     []
% 3.29/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.99  
% 3.29/0.99  ------ Combination Options
% 3.29/0.99  
% 3.29/0.99  --comb_res_mult                         3
% 3.29/0.99  --comb_sup_mult                         2
% 3.29/0.99  --comb_inst_mult                        10
% 3.29/0.99  
% 3.29/0.99  ------ Debug Options
% 3.29/0.99  
% 3.29/0.99  --dbg_backtrace                         false
% 3.29/0.99  --dbg_dump_prop_clauses                 false
% 3.29/0.99  --dbg_dump_prop_clauses_file            -
% 3.29/0.99  --dbg_out_stat                          false
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ Proving...
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS status Theorem for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  fof(f14,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f30,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.29/0.99    inference(ennf_transformation,[],[f14])).
% 3.29/0.99  
% 3.29/0.99  fof(f31,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.29/0.99    inference(flattening,[],[f30])).
% 3.29/0.99  
% 3.29/0.99  fof(f66,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f31])).
% 3.29/0.99  
% 3.29/0.99  fof(f11,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f26,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.29/0.99    inference(ennf_transformation,[],[f11])).
% 3.29/0.99  
% 3.29/0.99  fof(f27,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.99    inference(flattening,[],[f26])).
% 3.29/0.99  
% 3.29/0.99  fof(f42,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.99    inference(nnf_transformation,[],[f27])).
% 3.29/0.99  
% 3.29/0.99  fof(f60,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f42])).
% 3.29/0.99  
% 3.29/0.99  fof(f18,conjecture,(
% 3.29/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f19,negated_conjecture,(
% 3.29/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.29/0.99    inference(negated_conjecture,[],[f18])).
% 3.29/0.99  
% 3.29/0.99  fof(f36,plain,(
% 3.29/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.29/0.99    inference(ennf_transformation,[],[f19])).
% 3.29/0.99  
% 3.29/0.99  fof(f37,plain,(
% 3.29/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.29/0.99    inference(flattening,[],[f36])).
% 3.29/0.99  
% 3.29/0.99  fof(f45,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f44,plain,(
% 3.29/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f46,plain,(
% 3.29/0.99    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f45,f44])).
% 3.29/0.99  
% 3.29/0.99  fof(f77,plain,(
% 3.29/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f12,axiom,(
% 3.29/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f62,plain,(
% 3.29/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f12])).
% 3.29/0.99  
% 3.29/0.99  fof(f15,axiom,(
% 3.29/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f67,plain,(
% 3.29/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f15])).
% 3.29/0.99  
% 3.29/0.99  fof(f82,plain,(
% 3.29/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.29/0.99    inference(definition_unfolding,[],[f62,f67])).
% 3.29/0.99  
% 3.29/0.99  fof(f71,plain,(
% 3.29/0.99    v1_funct_1(sK3)),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f73,plain,(
% 3.29/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f74,plain,(
% 3.29/0.99    v1_funct_1(sK4)),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f76,plain,(
% 3.29/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f17,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f34,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.29/0.99    inference(ennf_transformation,[],[f17])).
% 3.29/0.99  
% 3.29/0.99  fof(f35,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.29/0.99    inference(flattening,[],[f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f69,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f35])).
% 3.29/0.99  
% 3.29/0.99  fof(f72,plain,(
% 3.29/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f75,plain,(
% 3.29/0.99    v1_funct_2(sK4,sK2,sK1)),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f5,axiom,(
% 3.29/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f23,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.29/0.99    inference(ennf_transformation,[],[f5])).
% 3.29/0.99  
% 3.29/0.99  fof(f53,plain,(
% 3.29/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f23])).
% 3.29/0.99  
% 3.29/0.99  fof(f6,axiom,(
% 3.29/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f54,plain,(
% 3.29/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f6])).
% 3.29/0.99  
% 3.29/0.99  fof(f10,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f25,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.99    inference(ennf_transformation,[],[f10])).
% 3.29/0.99  
% 3.29/0.99  fof(f59,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f25])).
% 3.29/0.99  
% 3.29/0.99  fof(f16,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f32,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.29/0.99    inference(ennf_transformation,[],[f16])).
% 3.29/0.99  
% 3.29/0.99  fof(f33,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.29/0.99    inference(flattening,[],[f32])).
% 3.29/0.99  
% 3.29/0.99  fof(f68,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f33])).
% 3.29/0.99  
% 3.29/0.99  fof(f9,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f20,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.29/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.29/0.99  
% 3.29/0.99  fof(f24,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/0.99    inference(ennf_transformation,[],[f20])).
% 3.29/0.99  
% 3.29/0.99  fof(f58,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f24])).
% 3.29/0.99  
% 3.29/0.99  fof(f13,axiom,(
% 3.29/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f28,plain,(
% 3.29/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.29/0.99    inference(ennf_transformation,[],[f13])).
% 3.29/0.99  
% 3.29/0.99  fof(f29,plain,(
% 3.29/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.29/0.99    inference(flattening,[],[f28])).
% 3.29/0.99  
% 3.29/0.99  fof(f43,plain,(
% 3.29/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.29/0.99    inference(nnf_transformation,[],[f29])).
% 3.29/0.99  
% 3.29/0.99  fof(f64,plain,(
% 3.29/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f43])).
% 3.29/0.99  
% 3.29/0.99  fof(f86,plain,(
% 3.29/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.29/0.99    inference(equality_resolution,[],[f64])).
% 3.29/0.99  
% 3.29/0.99  fof(f78,plain,(
% 3.29/0.99    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 3.29/0.99    inference(cnf_transformation,[],[f46])).
% 3.29/0.99  
% 3.29/0.99  fof(f8,axiom,(
% 3.29/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f57,plain,(
% 3.29/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f8])).
% 3.29/0.99  
% 3.29/0.99  fof(f80,plain,(
% 3.29/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.29/0.99    inference(definition_unfolding,[],[f57,f67])).
% 3.29/0.99  
% 3.29/0.99  fof(f3,axiom,(
% 3.29/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f40,plain,(
% 3.29/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.29/0.99    inference(nnf_transformation,[],[f3])).
% 3.29/0.99  
% 3.29/0.99  fof(f41,plain,(
% 3.29/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.29/0.99    inference(flattening,[],[f40])).
% 3.29/0.99  
% 3.29/0.99  fof(f50,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.29/0.99    inference(cnf_transformation,[],[f41])).
% 3.29/0.99  
% 3.29/0.99  fof(f84,plain,(
% 3.29/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.29/0.99    inference(equality_resolution,[],[f50])).
% 3.29/0.99  
% 3.29/0.99  fof(f2,axiom,(
% 3.29/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f21,plain,(
% 3.29/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.29/0.99    inference(ennf_transformation,[],[f2])).
% 3.29/0.99  
% 3.29/0.99  fof(f38,plain,(
% 3.29/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f39,plain,(
% 3.29/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f38])).
% 3.29/0.99  
% 3.29/0.99  fof(f48,plain,(
% 3.29/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.29/0.99    inference(cnf_transformation,[],[f39])).
% 3.29/0.99  
% 3.29/0.99  fof(f1,axiom,(
% 3.29/0.99    v1_xboole_0(k1_xboole_0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f47,plain,(
% 3.29/0.99    v1_xboole_0(k1_xboole_0)),
% 3.29/0.99    inference(cnf_transformation,[],[f1])).
% 3.29/0.99  
% 3.29/0.99  fof(f4,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f22,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.29/0.99    inference(ennf_transformation,[],[f4])).
% 3.29/0.99  
% 3.29/0.99  fof(f52,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f22])).
% 3.29/0.99  
% 3.29/0.99  fof(f49,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f41])).
% 3.29/0.99  
% 3.29/0.99  fof(f7,axiom,(
% 3.29/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f55,plain,(
% 3.29/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.29/0.99    inference(cnf_transformation,[],[f7])).
% 3.29/0.99  
% 3.29/0.99  fof(f79,plain,(
% 3.29/0.99    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.29/0.99    inference(definition_unfolding,[],[f55,f67])).
% 3.29/0.99  
% 3.29/0.99  cnf(c_18,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.29/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.29/0.99      | ~ v1_funct_1(X0)
% 3.29/0.99      | ~ v1_funct_1(X3) ),
% 3.29/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1098,plain,
% 3.29/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.29/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.29/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.29/0.99      | v1_funct_1(X0) != iProver_top
% 3.29/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_14,plain,
% 3.29/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.29/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.29/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.29/0.99      | X3 = X2 ),
% 3.29/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_24,negated_conjecture,
% 3.29/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_457,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | X3 = X0
% 3.29/0.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 3.29/0.99      | k6_partfun1(sK1) != X3
% 3.29/0.99      | sK1 != X2
% 3.29/0.99      | sK1 != X1 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_458,plain,
% 3.29/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.29/0.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.29/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_457]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_15,plain,
% 3.29/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.29/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_466,plain,
% 3.29/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.29/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.29/0.99      inference(forward_subsumption_resolution,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_458,c_15]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1084,plain,
% 3.29/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.29/0.99      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2916,plain,
% 3.29/0.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 3.29/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.29/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.29/0.99      | v1_funct_1(sK3) != iProver_top
% 3.29/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1098,c_1084]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_30,negated_conjecture,
% 3.29/0.99      ( v1_funct_1(sK3) ),
% 3.29/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_31,plain,
% 3.29/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_28,negated_conjecture,
% 3.29/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.29/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_33,plain,
% 3.29/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_27,negated_conjecture,
% 3.29/0.99      ( v1_funct_1(sK4) ),
% 3.29/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_34,plain,
% 3.29/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_25,negated_conjecture,
% 3.29/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.29/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_36,plain,
% 3.29/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2983,plain,
% 3.29/0.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_2916,c_31,c_33,c_34,c_36]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_22,plain,
% 3.29/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.29/0.99      | ~ v1_funct_2(X3,X4,X1)
% 3.29/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | ~ v1_funct_1(X0)
% 3.29/0.99      | ~ v1_funct_1(X3)
% 3.29/0.99      | v2_funct_1(X3)
% 3.29/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.29/0.99      | k1_xboole_0 = X2 ),
% 3.29/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1095,plain,
% 3.29/0.99      ( k1_xboole_0 = X0
% 3.29/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.29/0.99      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.29/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.29/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.29/0.99      | v1_funct_1(X1) != iProver_top
% 3.29/0.99      | v1_funct_1(X3) != iProver_top
% 3.29/0.99      | v2_funct_1(X3) = iProver_top
% 3.29/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3010,plain,
% 3.29/0.99      ( sK1 = k1_xboole_0
% 3.29/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.29/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.29/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.29/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.29/0.99      | v1_funct_1(sK3) != iProver_top
% 3.29/0.99      | v1_funct_1(sK4) != iProver_top
% 3.29/0.99      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.29/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_2983,c_1095]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_29,negated_conjecture,
% 3.29/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.29/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_32,plain,
% 3.29/0.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_26,negated_conjecture,
% 3.29/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_35,plain,
% 3.29/0.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.29/0.99      | ~ v1_relat_1(X1)
% 3.29/0.99      | v1_relat_1(X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1319,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | v1_relat_1(X0)
% 3.29/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1796,plain,
% 3.29/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.29/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 3.29/0.99      | v1_relat_1(sK4) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1319]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1797,plain,
% 3.29/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.29/0.99      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 3.29/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1796]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7,plain,
% 3.29/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1881,plain,
% 3.29/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1882,plain,
% 3.29/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1094,plain,
% 3.29/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_12,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1100,plain,
% 3.29/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.29/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2108,plain,
% 3.29/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1094,c_1100]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_20,plain,
% 3.29/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.29/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.29/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.29/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.29/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.29/0.99      | ~ v1_funct_1(X2)
% 3.29/0.99      | ~ v1_funct_1(X3)
% 3.29/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.29/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_470,plain,
% 3.29/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.29/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.29/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | ~ v1_funct_1(X0)
% 3.29/0.99      | ~ v1_funct_1(X3)
% 3.29/0.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.29/0.99      | k2_relset_1(X1,X2,X0) = X2
% 3.29/0.99      | k6_partfun1(X2) != k6_partfun1(sK1)
% 3.29/0.99      | sK1 != X2 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_471,plain,
% 3.29/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 3.29/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 3.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.29/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.29/0.99      | ~ v1_funct_1(X0)
% 3.29/0.99      | ~ v1_funct_1(X2)
% 3.29/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.29/0.99      | k2_relset_1(X1,sK1,X0) = sK1
% 3.29/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_470]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_546,plain,
% 3.29/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 3.29/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 3.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.29/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.29/0.99      | ~ v1_funct_1(X0)
% 3.29/0.99      | ~ v1_funct_1(X2)
% 3.29/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.29/0.99      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 3.29/0.99      inference(equality_resolution_simp,[status(thm)],[c_471]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1083,plain,
% 3.29/0.99      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.29/0.99      | k2_relset_1(X0,sK1,X2) = sK1
% 3.29/0.99      | v1_funct_2(X2,X0,sK1) != iProver_top
% 3.29/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.29/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.29/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.29/0.99      | v1_funct_1(X2) != iProver_top
% 3.29/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1852,plain,
% 3.29/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 3.29/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.29/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.29/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.29/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.29/0.99      | v1_funct_1(sK3) != iProver_top
% 3.29/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.29/0.99      inference(equality_resolution,[status(thm)],[c_1083]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1891,plain,
% 3.29/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_1852,c_31,c_32,c_33,c_34,c_35,c_36]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2123,plain,
% 3.29/0.99      ( k2_relat_1(sK4) = sK1 ),
% 3.29/0.99      inference(light_normalisation,[status(thm)],[c_2108,c_1891]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_11,plain,
% 3.29/0.99      ( v5_relat_1(X0,X1)
% 3.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.29/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_16,plain,
% 3.29/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.29/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.29/0.99      | ~ v1_relat_1(X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_23,negated_conjecture,
% 3.29/0.99      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 3.29/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_376,plain,
% 3.29/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.29/0.99      | ~ v2_funct_1(sK3)
% 3.29/0.99      | ~ v1_relat_1(X0)
% 3.29/0.99      | k2_relat_1(X0) != sK1
% 3.29/0.99      | sK4 != X0 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_377,plain,
% 3.29/0.99      ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
% 3.29/0.99      | ~ v2_funct_1(sK3)
% 3.29/0.99      | ~ v1_relat_1(sK4)
% 3.29/0.99      | k2_relat_1(sK4) != sK1 ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_376]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_397,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.99      | ~ v2_funct_1(sK3)
% 3.29/0.99      | ~ v1_relat_1(sK4)
% 3.29/0.99      | k2_relat_1(sK4) != X2
% 3.29/0.99      | k2_relat_1(sK4) != sK1
% 3.29/0.99      | sK4 != X0 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_377]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_398,plain,
% 3.29/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.29/0.99      | ~ v2_funct_1(sK3)
% 3.29/0.99      | ~ v1_relat_1(sK4)
% 3.29/0.99      | k2_relat_1(sK4) != sK1 ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_397]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_672,plain,
% 3.29/0.99      ( ~ v2_funct_1(sK3)
% 3.29/0.99      | ~ v1_relat_1(sK4)
% 3.29/0.99      | sP0_iProver_split
% 3.29/0.99      | k2_relat_1(sK4) != sK1 ),
% 3.29/0.99      inference(splitting,
% 3.29/0.99                [splitting(split),new_symbols(definition,[])],
% 3.29/0.99                [c_398]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1086,plain,
% 3.29/0.99      ( k2_relat_1(sK4) != sK1
% 3.29/0.99      | v2_funct_1(sK3) != iProver_top
% 3.29/0.99      | v1_relat_1(sK4) != iProver_top
% 3.29/0.99      | sP0_iProver_split = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2170,plain,
% 3.29/0.99      ( sK1 != sK1
% 3.29/0.99      | v2_funct_1(sK3) != iProver_top
% 3.29/0.99      | v1_relat_1(sK4) != iProver_top
% 3.29/0.99      | sP0_iProver_split = iProver_top ),
% 3.29/0.99      inference(demodulation,[status(thm)],[c_2123,c_1086]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2176,plain,
% 3.29/0.99      ( v2_funct_1(sK3) != iProver_top
% 3.29/0.99      | v1_relat_1(sK4) != iProver_top
% 3.29/0.99      | sP0_iProver_split = iProver_top ),
% 3.29/0.99      inference(equality_resolution_simp,[status(thm)],[c_2170]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_671,plain,
% 3.29/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.29/0.99      | ~ sP0_iProver_split ),
% 3.29/0.99      inference(splitting,
% 3.29/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.29/0.99                [c_398]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1087,plain,
% 3.29/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
% 3.29/0.99      | sP0_iProver_split != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2171,plain,
% 3.29/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.29/0.99      | sP0_iProver_split != iProver_top ),
% 3.29/0.99      inference(demodulation,[status(thm)],[c_2123,c_1087]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2190,plain,
% 3.29/0.99      ( sP0_iProver_split != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1094,c_2171]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6387,plain,
% 3.29/0.99      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top | sK1 = k1_xboole_0 ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_3010,c_31,c_32,c_33,c_34,c_35,c_36,c_1797,c_1882,
% 3.29/0.99                 c_2176,c_2190]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6388,plain,
% 3.29/0.99      ( sK1 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_6387]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_9,plain,
% 3.29/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1102,plain,
% 3.29/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6393,plain,
% 3.29/0.99      ( sK1 = k1_xboole_0 ),
% 3.29/0.99      inference(forward_subsumption_resolution,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_6388,c_1102]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1091,plain,
% 3.29/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6427,plain,
% 3.29/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 3.29/0.99      inference(demodulation,[status(thm)],[c_6393,c_1091]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3,plain,
% 3.29/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.29/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6435,plain,
% 3.29/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.29/0.99      inference(demodulation,[status(thm)],[c_6427,c_3]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_675,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1773,plain,
% 3.29/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_675]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2285,plain,
% 3.29/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1773]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2286,plain,
% 3.29/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_2285]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_681,plain,
% 3.29/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.29/0.99      theory(equality) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1973,plain,
% 3.29/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_681]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1974,plain,
% 3.29/0.99      ( sK3 != X0
% 3.29/0.99      | v2_funct_1(X0) != iProver_top
% 3.29/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1976,plain,
% 3.29/0.99      ( sK3 != k1_xboole_0
% 3.29/0.99      | v2_funct_1(sK3) = iProver_top
% 3.29/0.99      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1607,plain,
% 3.29/0.99      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_675]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1608,plain,
% 3.29/0.99      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.29/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.29/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1607]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_674,plain,( X0 = X0 ),theory(equality) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1498,plain,
% 3.29/0.99      ( sK3 = sK3 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_674]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1,plain,
% 3.29/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.29/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_0,plain,
% 3.29/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.29/0.99      | ~ r2_hidden(X2,X0)
% 3.29/0.99      | ~ v1_xboole_0(X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_305,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.29/0.99      | ~ r2_hidden(X2,X0)
% 3.29/0.99      | k1_xboole_0 != X1 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_306,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_305]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_320,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.29/0.99      | X0 != X1
% 3.29/0.99      | sK0(X1) != X2
% 3.29/0.99      | k1_xboole_0 = X1 ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_306]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_321,plain,
% 3.29/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 3.29/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1459,plain,
% 3.29/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK3 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_321]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1462,plain,
% 3.29/0.99      ( k1_xboole_0 = sK3
% 3.29/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1333,plain,
% 3.29/0.99      ( v2_funct_1(X0)
% 3.29/0.99      | ~ v2_funct_1(k6_partfun1(X1))
% 3.29/0.99      | X0 != k6_partfun1(X1) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_681]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1334,plain,
% 3.29/0.99      ( X0 != k6_partfun1(X1)
% 3.29/0.99      | v2_funct_1(X0) = iProver_top
% 3.29/0.99      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1336,plain,
% 3.29/0.99      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.29/0.99      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.29/0.99      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1334]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_89,plain,
% 3.29/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_4,plain,
% 3.29/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.29/0.99      | k1_xboole_0 = X0
% 3.29/0.99      | k1_xboole_0 = X1 ),
% 3.29/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_88,plain,
% 3.29/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.29/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_8,plain,
% 3.29/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.29/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_78,plain,
% 3.29/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_80,plain,
% 3.29/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_78]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(contradiction,plain,
% 3.29/0.99      ( $false ),
% 3.29/0.99      inference(minisat,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_6435,c_2286,c_2190,c_2176,c_1976,c_1882,c_1797,c_1608,
% 3.29/0.99                 c_1498,c_1462,c_1336,c_89,c_88,c_8,c_80,c_36]) ).
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  ------                               Statistics
% 3.29/0.99  
% 3.29/0.99  ------ General
% 3.29/0.99  
% 3.29/0.99  abstr_ref_over_cycles:                  0
% 3.29/0.99  abstr_ref_under_cycles:                 0
% 3.29/0.99  gc_basic_clause_elim:                   0
% 3.29/0.99  forced_gc_time:                         0
% 3.29/0.99  parsing_time:                           0.01
% 3.29/0.99  unif_index_cands_time:                  0.
% 3.29/0.99  unif_index_add_time:                    0.
% 3.29/0.99  orderings_time:                         0.
% 3.29/0.99  out_proof_time:                         0.011
% 3.29/0.99  total_time:                             0.253
% 3.29/0.99  num_of_symbols:                         54
% 3.29/0.99  num_of_terms:                           9025
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing
% 3.29/0.99  
% 3.29/0.99  num_of_splits:                          1
% 3.29/0.99  num_of_split_atoms:                     1
% 3.29/0.99  num_of_reused_defs:                     0
% 3.29/0.99  num_eq_ax_congr_red:                    11
% 3.29/0.99  num_of_sem_filtered_clauses:            1
% 3.29/0.99  num_of_subtypes:                        0
% 3.29/0.99  monotx_restored_types:                  0
% 3.29/0.99  sat_num_of_epr_types:                   0
% 3.29/0.99  sat_num_of_non_cyclic_types:            0
% 3.29/0.99  sat_guarded_non_collapsed_types:        0
% 3.29/0.99  num_pure_diseq_elim:                    0
% 3.29/0.99  simp_replaced_by:                       0
% 3.29/0.99  res_preprocessed:                       135
% 3.29/0.99  prep_upred:                             0
% 3.29/0.99  prep_unflattend:                        22
% 3.29/0.99  smt_new_axioms:                         0
% 3.29/0.99  pred_elim_cands:                        5
% 3.29/0.99  pred_elim:                              5
% 3.29/0.99  pred_elim_cl:                           6
% 3.29/0.99  pred_elim_cycles:                       8
% 3.29/0.99  merged_defs:                            0
% 3.29/0.99  merged_defs_ncl:                        0
% 3.29/0.99  bin_hyper_res:                          0
% 3.29/0.99  prep_cycles:                            4
% 3.29/0.99  pred_elim_time:                         0.006
% 3.29/0.99  splitting_time:                         0.
% 3.29/0.99  sem_filter_time:                        0.
% 3.29/0.99  monotx_time:                            0.001
% 3.29/0.99  subtype_inf_time:                       0.
% 3.29/0.99  
% 3.29/0.99  ------ Problem properties
% 3.29/0.99  
% 3.29/0.99  clauses:                                26
% 3.29/0.99  conjectures:                            6
% 3.29/0.99  epr:                                    4
% 3.29/0.99  horn:                                   24
% 3.29/0.99  ground:                                 9
% 3.29/0.99  unary:                                  13
% 3.29/0.99  binary:                                 4
% 3.29/0.99  lits:                                   74
% 3.29/0.99  lits_eq:                                15
% 3.29/0.99  fd_pure:                                0
% 3.29/0.99  fd_pseudo:                              0
% 3.29/0.99  fd_cond:                                3
% 3.29/0.99  fd_pseudo_cond:                         0
% 3.29/0.99  ac_symbols:                             0
% 3.29/0.99  
% 3.29/0.99  ------ Propositional Solver
% 3.29/0.99  
% 3.29/0.99  prop_solver_calls:                      29
% 3.29/0.99  prop_fast_solver_calls:                 1147
% 3.29/0.99  smt_solver_calls:                       0
% 3.29/0.99  smt_fast_solver_calls:                  0
% 3.29/0.99  prop_num_of_clauses:                    2420
% 3.29/0.99  prop_preprocess_simplified:             6226
% 3.29/0.99  prop_fo_subsumed:                       37
% 3.29/0.99  prop_solver_time:                       0.
% 3.29/0.99  smt_solver_time:                        0.
% 3.29/0.99  smt_fast_solver_time:                   0.
% 3.29/0.99  prop_fast_solver_time:                  0.
% 3.29/0.99  prop_unsat_core_time:                   0.
% 3.29/0.99  
% 3.29/0.99  ------ QBF
% 3.29/0.99  
% 3.29/0.99  qbf_q_res:                              0
% 3.29/0.99  qbf_num_tautologies:                    0
% 3.29/0.99  qbf_prep_cycles:                        0
% 3.29/0.99  
% 3.29/0.99  ------ BMC1
% 3.29/0.99  
% 3.29/0.99  bmc1_current_bound:                     -1
% 3.29/0.99  bmc1_last_solved_bound:                 -1
% 3.29/0.99  bmc1_unsat_core_size:                   -1
% 3.29/0.99  bmc1_unsat_core_parents_size:           -1
% 3.29/0.99  bmc1_merge_next_fun:                    0
% 3.29/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.29/0.99  
% 3.29/0.99  ------ Instantiation
% 3.29/0.99  
% 3.29/0.99  inst_num_of_clauses:                    775
% 3.29/0.99  inst_num_in_passive:                    266
% 3.29/0.99  inst_num_in_active:                     410
% 3.29/0.99  inst_num_in_unprocessed:                99
% 3.29/0.99  inst_num_of_loops:                      430
% 3.29/0.99  inst_num_of_learning_restarts:          0
% 3.29/0.99  inst_num_moves_active_passive:          16
% 3.29/0.99  inst_lit_activity:                      0
% 3.29/0.99  inst_lit_activity_moves:                0
% 3.29/0.99  inst_num_tautologies:                   0
% 3.29/0.99  inst_num_prop_implied:                  0
% 3.29/0.99  inst_num_existing_simplified:           0
% 3.29/0.99  inst_num_eq_res_simplified:             0
% 3.29/0.99  inst_num_child_elim:                    0
% 3.29/0.99  inst_num_of_dismatching_blockings:      117
% 3.29/0.99  inst_num_of_non_proper_insts:           512
% 3.29/0.99  inst_num_of_duplicates:                 0
% 3.29/0.99  inst_inst_num_from_inst_to_res:         0
% 3.29/0.99  inst_dismatching_checking_time:         0.
% 3.29/0.99  
% 3.29/0.99  ------ Resolution
% 3.29/0.99  
% 3.29/0.99  res_num_of_clauses:                     0
% 3.29/0.99  res_num_in_passive:                     0
% 3.29/0.99  res_num_in_active:                      0
% 3.29/0.99  res_num_of_loops:                       139
% 3.29/0.99  res_forward_subset_subsumed:            26
% 3.29/0.99  res_backward_subset_subsumed:           0
% 3.29/0.99  res_forward_subsumed:                   0
% 3.29/0.99  res_backward_subsumed:                  0
% 3.29/0.99  res_forward_subsumption_resolution:     2
% 3.29/0.99  res_backward_subsumption_resolution:    0
% 3.29/0.99  res_clause_to_clause_subsumption:       1342
% 3.29/0.99  res_orphan_elimination:                 0
% 3.29/0.99  res_tautology_del:                      30
% 3.29/0.99  res_num_eq_res_simplified:              1
% 3.29/0.99  res_num_sel_changes:                    0
% 3.29/0.99  res_moves_from_active_to_pass:          0
% 3.29/0.99  
% 3.29/0.99  ------ Superposition
% 3.29/0.99  
% 3.29/0.99  sup_time_total:                         0.
% 3.29/0.99  sup_time_generating:                    0.
% 3.29/0.99  sup_time_sim_full:                      0.
% 3.29/0.99  sup_time_sim_immed:                     0.
% 3.29/0.99  
% 3.29/0.99  sup_num_of_clauses:                     131
% 3.29/0.99  sup_num_in_active:                      39
% 3.29/0.99  sup_num_in_passive:                     92
% 3.29/0.99  sup_num_of_loops:                       84
% 3.29/0.99  sup_fw_superposition:                   117
% 3.29/0.99  sup_bw_superposition:                   16
% 3.29/0.99  sup_immediate_simplified:               33
% 3.29/0.99  sup_given_eliminated:                   1
% 3.29/0.99  comparisons_done:                       0
% 3.29/0.99  comparisons_avoided:                    0
% 3.29/0.99  
% 3.29/0.99  ------ Simplifications
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  sim_fw_subset_subsumed:                 1
% 3.29/0.99  sim_bw_subset_subsumed:                 9
% 3.29/0.99  sim_fw_subsumed:                        3
% 3.29/0.99  sim_bw_subsumed:                        1
% 3.29/0.99  sim_fw_subsumption_res:                 6
% 3.29/0.99  sim_bw_subsumption_res:                 0
% 3.29/0.99  sim_tautology_del:                      1
% 3.29/0.99  sim_eq_tautology_del:                   4
% 3.29/0.99  sim_eq_res_simp:                        1
% 3.29/0.99  sim_fw_demodulated:                     15
% 3.29/0.99  sim_bw_demodulated:                     40
% 3.29/0.99  sim_light_normalised:                   7
% 3.29/0.99  sim_joinable_taut:                      0
% 3.29/0.99  sim_joinable_simp:                      0
% 3.29/0.99  sim_ac_normalised:                      0
% 3.29/0.99  sim_smt_subsumption:                    0
% 3.29/0.99  
%------------------------------------------------------------------------------
