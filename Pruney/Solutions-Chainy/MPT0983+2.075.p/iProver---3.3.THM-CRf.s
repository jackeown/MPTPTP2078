%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:00 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  191 (1327 expanded)
%              Number of clauses        :  110 ( 400 expanded)
%              Number of leaves         :   23 ( 326 expanded)
%              Depth                    :   22
%              Number of atoms          :  618 (8307 expanded)
%              Number of equality atoms :  234 ( 734 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f47,f46])).

fof(f83,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f41])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1428,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_531,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_539,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_531,c_19])).

cnf(c_1415,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_3741,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_1415])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2140,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2580,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_1415])).

cnf(c_2597,plain,
    ( ~ r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1))
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2580])).

cnf(c_1754,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1941,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_2356,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,X0,X1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_3251,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_4215,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3741,c_34,c_32,c_31,c_29,c_2140,c_2597,c_3251])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1425,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4242,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4215,c_1425])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1424,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1430,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2859,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1424,c_1430])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_543,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_544,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_620,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_544])).

cnf(c_1414,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_2170,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1414])).

cnf(c_2227,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2170,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_2877,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2859,c_2227])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_448,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_449,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_459,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_449,c_14])).

cnf(c_27,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_459,c_27])).

cnf(c_475,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_815,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_475])).

cnf(c_1417,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_3274,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2877,c_1417])).

cnf(c_3275,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3274])).

cnf(c_814,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_475])).

cnf(c_1418,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_3273,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2877,c_1418])).

cnf(c_3406,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1424,c_3273])).

cnf(c_4368,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4242,c_35,c_36,c_37,c_38,c_39,c_40,c_3275,c_3406])).

cnf(c_4369,plain,
    ( sK1 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4368])).

cnf(c_12,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1431,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4374,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4369,c_1431])).

cnf(c_1421,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1432,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2505,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1432])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1436,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3155,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2505,c_1436])).

cnf(c_4378,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4374,c_3155])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4418,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4378,c_5])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_87,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_11,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_100,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_823,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1666,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_1667,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1666])).

cnf(c_1669,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_818,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1911,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1912,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_2084,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2085,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2084])).

cnf(c_2087,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_2415,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_2416,plain,
    ( sK3 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_2418,plain,
    ( sK3 != k1_xboole_0
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_4382,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4374,c_2505])).

cnf(c_4405,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4382,c_5])).

cnf(c_5364,plain,
    ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4418,c_87,c_11,c_100,c_101,c_1669,c_1912,c_2087,c_2418,c_3275,c_3406,c_4405])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1434,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_422,plain,
    ( sK0(X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_423,plain,
    ( k1_xboole_0 = sK0(X0) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1457,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1434,c_423])).

cnf(c_2506,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1457,c_1432])).

cnf(c_5369,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5364,c_2506])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:21:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/0.98  
% 3.16/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.98  
% 3.16/0.98  ------  iProver source info
% 3.16/0.98  
% 3.16/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.98  git: non_committed_changes: false
% 3.16/0.98  git: last_make_outside_of_git: false
% 3.16/0.98  
% 3.16/0.98  ------ 
% 3.16/0.98  
% 3.16/0.98  ------ Input Options
% 3.16/0.98  
% 3.16/0.98  --out_options                           all
% 3.16/0.98  --tptp_safe_out                         true
% 3.16/0.98  --problem_path                          ""
% 3.16/0.98  --include_path                          ""
% 3.16/0.98  --clausifier                            res/vclausify_rel
% 3.16/0.98  --clausifier_options                    --mode clausify
% 3.16/0.98  --stdin                                 false
% 3.16/0.98  --stats_out                             all
% 3.16/0.98  
% 3.16/0.98  ------ General Options
% 3.16/0.98  
% 3.16/0.98  --fof                                   false
% 3.16/0.98  --time_out_real                         305.
% 3.16/0.98  --time_out_virtual                      -1.
% 3.16/0.98  --symbol_type_check                     false
% 3.16/0.98  --clausify_out                          false
% 3.16/0.98  --sig_cnt_out                           false
% 3.16/0.98  --trig_cnt_out                          false
% 3.16/0.98  --trig_cnt_out_tolerance                1.
% 3.16/0.98  --trig_cnt_out_sk_spl                   false
% 3.16/0.98  --abstr_cl_out                          false
% 3.16/0.98  
% 3.16/0.98  ------ Global Options
% 3.16/0.98  
% 3.16/0.98  --schedule                              default
% 3.16/0.98  --add_important_lit                     false
% 3.16/0.98  --prop_solver_per_cl                    1000
% 3.16/0.98  --min_unsat_core                        false
% 3.16/0.98  --soft_assumptions                      false
% 3.16/0.98  --soft_lemma_size                       3
% 3.16/0.98  --prop_impl_unit_size                   0
% 3.16/0.98  --prop_impl_unit                        []
% 3.16/0.98  --share_sel_clauses                     true
% 3.16/0.98  --reset_solvers                         false
% 3.16/0.98  --bc_imp_inh                            [conj_cone]
% 3.16/0.98  --conj_cone_tolerance                   3.
% 3.16/0.98  --extra_neg_conj                        none
% 3.16/0.98  --large_theory_mode                     true
% 3.16/0.98  --prolific_symb_bound                   200
% 3.16/0.98  --lt_threshold                          2000
% 3.16/0.98  --clause_weak_htbl                      true
% 3.16/0.98  --gc_record_bc_elim                     false
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing Options
% 3.16/0.98  
% 3.16/0.98  --preprocessing_flag                    true
% 3.16/0.98  --time_out_prep_mult                    0.1
% 3.16/0.98  --splitting_mode                        input
% 3.16/0.98  --splitting_grd                         true
% 3.16/0.98  --splitting_cvd                         false
% 3.16/0.98  --splitting_cvd_svl                     false
% 3.16/0.98  --splitting_nvd                         32
% 3.16/0.98  --sub_typing                            true
% 3.16/0.98  --prep_gs_sim                           true
% 3.16/0.98  --prep_unflatten                        true
% 3.16/0.98  --prep_res_sim                          true
% 3.16/0.98  --prep_upred                            true
% 3.16/0.98  --prep_sem_filter                       exhaustive
% 3.16/0.98  --prep_sem_filter_out                   false
% 3.16/0.98  --pred_elim                             true
% 3.16/0.98  --res_sim_input                         true
% 3.16/0.98  --eq_ax_congr_red                       true
% 3.16/0.98  --pure_diseq_elim                       true
% 3.16/0.98  --brand_transform                       false
% 3.16/0.98  --non_eq_to_eq                          false
% 3.16/0.98  --prep_def_merge                        true
% 3.16/0.98  --prep_def_merge_prop_impl              false
% 3.16/0.98  --prep_def_merge_mbd                    true
% 3.16/0.98  --prep_def_merge_tr_red                 false
% 3.16/0.98  --prep_def_merge_tr_cl                  false
% 3.16/0.98  --smt_preprocessing                     true
% 3.16/0.98  --smt_ac_axioms                         fast
% 3.16/0.98  --preprocessed_out                      false
% 3.16/0.98  --preprocessed_stats                    false
% 3.16/0.98  
% 3.16/0.98  ------ Abstraction refinement Options
% 3.16/0.98  
% 3.16/0.98  --abstr_ref                             []
% 3.16/0.98  --abstr_ref_prep                        false
% 3.16/0.98  --abstr_ref_until_sat                   false
% 3.16/0.98  --abstr_ref_sig_restrict                funpre
% 3.16/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.98  --abstr_ref_under                       []
% 3.16/0.98  
% 3.16/0.98  ------ SAT Options
% 3.16/0.98  
% 3.16/0.98  --sat_mode                              false
% 3.16/0.98  --sat_fm_restart_options                ""
% 3.16/0.98  --sat_gr_def                            false
% 3.16/0.98  --sat_epr_types                         true
% 3.16/0.98  --sat_non_cyclic_types                  false
% 3.16/0.98  --sat_finite_models                     false
% 3.16/0.98  --sat_fm_lemmas                         false
% 3.16/0.98  --sat_fm_prep                           false
% 3.16/0.98  --sat_fm_uc_incr                        true
% 3.16/0.98  --sat_out_model                         small
% 3.16/0.98  --sat_out_clauses                       false
% 3.16/0.98  
% 3.16/0.98  ------ QBF Options
% 3.16/0.98  
% 3.16/0.98  --qbf_mode                              false
% 3.16/0.98  --qbf_elim_univ                         false
% 3.16/0.98  --qbf_dom_inst                          none
% 3.16/0.98  --qbf_dom_pre_inst                      false
% 3.16/0.98  --qbf_sk_in                             false
% 3.16/0.98  --qbf_pred_elim                         true
% 3.16/0.98  --qbf_split                             512
% 3.16/0.98  
% 3.16/0.98  ------ BMC1 Options
% 3.16/0.98  
% 3.16/0.98  --bmc1_incremental                      false
% 3.16/0.98  --bmc1_axioms                           reachable_all
% 3.16/0.98  --bmc1_min_bound                        0
% 3.16/0.98  --bmc1_max_bound                        -1
% 3.16/0.98  --bmc1_max_bound_default                -1
% 3.16/0.98  --bmc1_symbol_reachability              true
% 3.16/0.98  --bmc1_property_lemmas                  false
% 3.16/0.98  --bmc1_k_induction                      false
% 3.16/0.98  --bmc1_non_equiv_states                 false
% 3.16/0.98  --bmc1_deadlock                         false
% 3.16/0.98  --bmc1_ucm                              false
% 3.16/0.98  --bmc1_add_unsat_core                   none
% 3.16/0.98  --bmc1_unsat_core_children              false
% 3.16/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.98  --bmc1_out_stat                         full
% 3.16/0.98  --bmc1_ground_init                      false
% 3.16/0.98  --bmc1_pre_inst_next_state              false
% 3.16/0.98  --bmc1_pre_inst_state                   false
% 3.16/0.98  --bmc1_pre_inst_reach_state             false
% 3.16/0.98  --bmc1_out_unsat_core                   false
% 3.16/0.98  --bmc1_aig_witness_out                  false
% 3.16/0.98  --bmc1_verbose                          false
% 3.16/0.98  --bmc1_dump_clauses_tptp                false
% 3.16/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.98  --bmc1_dump_file                        -
% 3.16/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.98  --bmc1_ucm_extend_mode                  1
% 3.16/0.98  --bmc1_ucm_init_mode                    2
% 3.16/0.98  --bmc1_ucm_cone_mode                    none
% 3.16/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.98  --bmc1_ucm_relax_model                  4
% 3.16/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.98  --bmc1_ucm_layered_model                none
% 3.16/0.98  --bmc1_ucm_max_lemma_size               10
% 3.16/0.98  
% 3.16/0.98  ------ AIG Options
% 3.16/0.98  
% 3.16/0.98  --aig_mode                              false
% 3.16/0.98  
% 3.16/0.98  ------ Instantiation Options
% 3.16/0.98  
% 3.16/0.98  --instantiation_flag                    true
% 3.16/0.98  --inst_sos_flag                         false
% 3.16/0.98  --inst_sos_phase                        true
% 3.16/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel_side                     num_symb
% 3.16/0.98  --inst_solver_per_active                1400
% 3.16/0.98  --inst_solver_calls_frac                1.
% 3.16/0.98  --inst_passive_queue_type               priority_queues
% 3.16/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.98  --inst_passive_queues_freq              [25;2]
% 3.16/0.98  --inst_dismatching                      true
% 3.16/0.98  --inst_eager_unprocessed_to_passive     true
% 3.16/0.98  --inst_prop_sim_given                   true
% 3.16/0.98  --inst_prop_sim_new                     false
% 3.16/0.98  --inst_subs_new                         false
% 3.16/0.98  --inst_eq_res_simp                      false
% 3.16/0.98  --inst_subs_given                       false
% 3.16/0.98  --inst_orphan_elimination               true
% 3.16/0.98  --inst_learning_loop_flag               true
% 3.16/0.98  --inst_learning_start                   3000
% 3.16/0.98  --inst_learning_factor                  2
% 3.16/0.98  --inst_start_prop_sim_after_learn       3
% 3.16/0.98  --inst_sel_renew                        solver
% 3.16/0.98  --inst_lit_activity_flag                true
% 3.16/0.98  --inst_restr_to_given                   false
% 3.16/0.98  --inst_activity_threshold               500
% 3.16/0.98  --inst_out_proof                        true
% 3.16/0.98  
% 3.16/0.98  ------ Resolution Options
% 3.16/0.98  
% 3.16/0.98  --resolution_flag                       true
% 3.16/0.98  --res_lit_sel                           adaptive
% 3.16/0.98  --res_lit_sel_side                      none
% 3.16/0.98  --res_ordering                          kbo
% 3.16/0.98  --res_to_prop_solver                    active
% 3.16/0.98  --res_prop_simpl_new                    false
% 3.16/0.98  --res_prop_simpl_given                  true
% 3.16/0.98  --res_passive_queue_type                priority_queues
% 3.16/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.98  --res_passive_queues_freq               [15;5]
% 3.16/0.98  --res_forward_subs                      full
% 3.16/0.98  --res_backward_subs                     full
% 3.16/0.98  --res_forward_subs_resolution           true
% 3.16/0.98  --res_backward_subs_resolution          true
% 3.16/0.98  --res_orphan_elimination                true
% 3.16/0.98  --res_time_limit                        2.
% 3.16/0.98  --res_out_proof                         true
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Options
% 3.16/0.98  
% 3.16/0.98  --superposition_flag                    true
% 3.16/0.98  --sup_passive_queue_type                priority_queues
% 3.16/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.98  --demod_completeness_check              fast
% 3.16/0.98  --demod_use_ground                      true
% 3.16/0.98  --sup_to_prop_solver                    passive
% 3.16/0.98  --sup_prop_simpl_new                    true
% 3.16/0.98  --sup_prop_simpl_given                  true
% 3.16/0.98  --sup_fun_splitting                     false
% 3.16/0.98  --sup_smt_interval                      50000
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Simplification Setup
% 3.16/0.98  
% 3.16/0.98  --sup_indices_passive                   []
% 3.16/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_full_bw                           [BwDemod]
% 3.16/0.98  --sup_immed_triv                        [TrivRules]
% 3.16/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_immed_bw_main                     []
% 3.16/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  
% 3.16/0.98  ------ Combination Options
% 3.16/0.98  
% 3.16/0.98  --comb_res_mult                         3
% 3.16/0.98  --comb_sup_mult                         2
% 3.16/0.98  --comb_inst_mult                        10
% 3.16/0.98  
% 3.16/0.98  ------ Debug Options
% 3.16/0.98  
% 3.16/0.98  --dbg_backtrace                         false
% 3.16/0.98  --dbg_dump_prop_clauses                 false
% 3.16/0.98  --dbg_dump_prop_clauses_file            -
% 3.16/0.98  --dbg_out_stat                          false
% 3.16/0.98  ------ Parsing...
% 3.16/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.98  ------ Proving...
% 3.16/0.98  ------ Problem Properties 
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  clauses                                 28
% 3.16/0.98  conjectures                             6
% 3.16/0.98  EPR                                     6
% 3.16/0.98  Horn                                    26
% 3.16/0.98  unary                                   14
% 3.16/0.98  binary                                  5
% 3.16/0.98  lits                                    76
% 3.16/0.98  lits eq                                 16
% 3.16/0.98  fd_pure                                 0
% 3.16/0.98  fd_pseudo                               0
% 3.16/0.98  fd_cond                                 2
% 3.16/0.98  fd_pseudo_cond                          1
% 3.16/0.98  AC symbols                              0
% 3.16/0.98  
% 3.16/0.98  ------ Schedule dynamic 5 is on 
% 3.16/0.98  
% 3.16/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  ------ 
% 3.16/0.98  Current options:
% 3.16/0.98  ------ 
% 3.16/0.98  
% 3.16/0.98  ------ Input Options
% 3.16/0.98  
% 3.16/0.98  --out_options                           all
% 3.16/0.98  --tptp_safe_out                         true
% 3.16/0.98  --problem_path                          ""
% 3.16/0.98  --include_path                          ""
% 3.16/0.98  --clausifier                            res/vclausify_rel
% 3.16/0.98  --clausifier_options                    --mode clausify
% 3.16/0.98  --stdin                                 false
% 3.16/0.98  --stats_out                             all
% 3.16/0.98  
% 3.16/0.98  ------ General Options
% 3.16/0.98  
% 3.16/0.98  --fof                                   false
% 3.16/0.98  --time_out_real                         305.
% 3.16/0.98  --time_out_virtual                      -1.
% 3.16/0.98  --symbol_type_check                     false
% 3.16/0.98  --clausify_out                          false
% 3.16/0.98  --sig_cnt_out                           false
% 3.16/0.98  --trig_cnt_out                          false
% 3.16/0.98  --trig_cnt_out_tolerance                1.
% 3.16/0.98  --trig_cnt_out_sk_spl                   false
% 3.16/0.98  --abstr_cl_out                          false
% 3.16/0.98  
% 3.16/0.98  ------ Global Options
% 3.16/0.98  
% 3.16/0.98  --schedule                              default
% 3.16/0.98  --add_important_lit                     false
% 3.16/0.98  --prop_solver_per_cl                    1000
% 3.16/0.98  --min_unsat_core                        false
% 3.16/0.98  --soft_assumptions                      false
% 3.16/0.98  --soft_lemma_size                       3
% 3.16/0.98  --prop_impl_unit_size                   0
% 3.16/0.98  --prop_impl_unit                        []
% 3.16/0.98  --share_sel_clauses                     true
% 3.16/0.98  --reset_solvers                         false
% 3.16/0.98  --bc_imp_inh                            [conj_cone]
% 3.16/0.98  --conj_cone_tolerance                   3.
% 3.16/0.98  --extra_neg_conj                        none
% 3.16/0.98  --large_theory_mode                     true
% 3.16/0.98  --prolific_symb_bound                   200
% 3.16/0.98  --lt_threshold                          2000
% 3.16/0.98  --clause_weak_htbl                      true
% 3.16/0.98  --gc_record_bc_elim                     false
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing Options
% 3.16/0.98  
% 3.16/0.98  --preprocessing_flag                    true
% 3.16/0.98  --time_out_prep_mult                    0.1
% 3.16/0.98  --splitting_mode                        input
% 3.16/0.98  --splitting_grd                         true
% 3.16/0.98  --splitting_cvd                         false
% 3.16/0.98  --splitting_cvd_svl                     false
% 3.16/0.98  --splitting_nvd                         32
% 3.16/0.98  --sub_typing                            true
% 3.16/0.98  --prep_gs_sim                           true
% 3.16/0.98  --prep_unflatten                        true
% 3.16/0.98  --prep_res_sim                          true
% 3.16/0.98  --prep_upred                            true
% 3.16/0.98  --prep_sem_filter                       exhaustive
% 3.16/0.98  --prep_sem_filter_out                   false
% 3.16/0.98  --pred_elim                             true
% 3.16/0.98  --res_sim_input                         true
% 3.16/0.98  --eq_ax_congr_red                       true
% 3.16/0.98  --pure_diseq_elim                       true
% 3.16/0.98  --brand_transform                       false
% 3.16/0.98  --non_eq_to_eq                          false
% 3.16/0.98  --prep_def_merge                        true
% 3.16/0.98  --prep_def_merge_prop_impl              false
% 3.16/0.98  --prep_def_merge_mbd                    true
% 3.16/0.98  --prep_def_merge_tr_red                 false
% 3.16/0.98  --prep_def_merge_tr_cl                  false
% 3.16/0.98  --smt_preprocessing                     true
% 3.16/0.98  --smt_ac_axioms                         fast
% 3.16/0.98  --preprocessed_out                      false
% 3.16/0.98  --preprocessed_stats                    false
% 3.16/0.98  
% 3.16/0.98  ------ Abstraction refinement Options
% 3.16/0.98  
% 3.16/0.98  --abstr_ref                             []
% 3.16/0.98  --abstr_ref_prep                        false
% 3.16/0.98  --abstr_ref_until_sat                   false
% 3.16/0.98  --abstr_ref_sig_restrict                funpre
% 3.16/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.98  --abstr_ref_under                       []
% 3.16/0.98  
% 3.16/0.98  ------ SAT Options
% 3.16/0.98  
% 3.16/0.98  --sat_mode                              false
% 3.16/0.98  --sat_fm_restart_options                ""
% 3.16/0.98  --sat_gr_def                            false
% 3.16/0.98  --sat_epr_types                         true
% 3.16/0.98  --sat_non_cyclic_types                  false
% 3.16/0.98  --sat_finite_models                     false
% 3.16/0.98  --sat_fm_lemmas                         false
% 3.16/0.98  --sat_fm_prep                           false
% 3.16/0.98  --sat_fm_uc_incr                        true
% 3.16/0.98  --sat_out_model                         small
% 3.16/0.98  --sat_out_clauses                       false
% 3.16/0.98  
% 3.16/0.98  ------ QBF Options
% 3.16/0.98  
% 3.16/0.98  --qbf_mode                              false
% 3.16/0.98  --qbf_elim_univ                         false
% 3.16/0.98  --qbf_dom_inst                          none
% 3.16/0.98  --qbf_dom_pre_inst                      false
% 3.16/0.98  --qbf_sk_in                             false
% 3.16/0.98  --qbf_pred_elim                         true
% 3.16/0.98  --qbf_split                             512
% 3.16/0.98  
% 3.16/0.98  ------ BMC1 Options
% 3.16/0.98  
% 3.16/0.98  --bmc1_incremental                      false
% 3.16/0.98  --bmc1_axioms                           reachable_all
% 3.16/0.98  --bmc1_min_bound                        0
% 3.16/0.98  --bmc1_max_bound                        -1
% 3.16/0.98  --bmc1_max_bound_default                -1
% 3.16/0.98  --bmc1_symbol_reachability              true
% 3.16/0.98  --bmc1_property_lemmas                  false
% 3.16/0.98  --bmc1_k_induction                      false
% 3.16/0.98  --bmc1_non_equiv_states                 false
% 3.16/0.98  --bmc1_deadlock                         false
% 3.16/0.98  --bmc1_ucm                              false
% 3.16/0.98  --bmc1_add_unsat_core                   none
% 3.16/0.98  --bmc1_unsat_core_children              false
% 3.16/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.98  --bmc1_out_stat                         full
% 3.16/0.98  --bmc1_ground_init                      false
% 3.16/0.98  --bmc1_pre_inst_next_state              false
% 3.16/0.98  --bmc1_pre_inst_state                   false
% 3.16/0.98  --bmc1_pre_inst_reach_state             false
% 3.16/0.98  --bmc1_out_unsat_core                   false
% 3.16/0.98  --bmc1_aig_witness_out                  false
% 3.16/0.98  --bmc1_verbose                          false
% 3.16/0.98  --bmc1_dump_clauses_tptp                false
% 3.16/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.98  --bmc1_dump_file                        -
% 3.16/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.98  --bmc1_ucm_extend_mode                  1
% 3.16/0.98  --bmc1_ucm_init_mode                    2
% 3.16/0.98  --bmc1_ucm_cone_mode                    none
% 3.16/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.98  --bmc1_ucm_relax_model                  4
% 3.16/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.98  --bmc1_ucm_layered_model                none
% 3.16/0.98  --bmc1_ucm_max_lemma_size               10
% 3.16/0.98  
% 3.16/0.98  ------ AIG Options
% 3.16/0.98  
% 3.16/0.98  --aig_mode                              false
% 3.16/0.98  
% 3.16/0.98  ------ Instantiation Options
% 3.16/0.98  
% 3.16/0.98  --instantiation_flag                    true
% 3.16/0.98  --inst_sos_flag                         false
% 3.16/0.98  --inst_sos_phase                        true
% 3.16/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.98  --inst_lit_sel_side                     none
% 3.16/0.98  --inst_solver_per_active                1400
% 3.16/0.98  --inst_solver_calls_frac                1.
% 3.16/0.98  --inst_passive_queue_type               priority_queues
% 3.16/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.98  --inst_passive_queues_freq              [25;2]
% 3.16/0.98  --inst_dismatching                      true
% 3.16/0.98  --inst_eager_unprocessed_to_passive     true
% 3.16/0.98  --inst_prop_sim_given                   true
% 3.16/0.98  --inst_prop_sim_new                     false
% 3.16/0.98  --inst_subs_new                         false
% 3.16/0.98  --inst_eq_res_simp                      false
% 3.16/0.98  --inst_subs_given                       false
% 3.16/0.98  --inst_orphan_elimination               true
% 3.16/0.98  --inst_learning_loop_flag               true
% 3.16/0.98  --inst_learning_start                   3000
% 3.16/0.98  --inst_learning_factor                  2
% 3.16/0.98  --inst_start_prop_sim_after_learn       3
% 3.16/0.98  --inst_sel_renew                        solver
% 3.16/0.98  --inst_lit_activity_flag                true
% 3.16/0.98  --inst_restr_to_given                   false
% 3.16/0.98  --inst_activity_threshold               500
% 3.16/0.98  --inst_out_proof                        true
% 3.16/0.98  
% 3.16/0.98  ------ Resolution Options
% 3.16/0.98  
% 3.16/0.98  --resolution_flag                       false
% 3.16/0.98  --res_lit_sel                           adaptive
% 3.16/0.98  --res_lit_sel_side                      none
% 3.16/0.98  --res_ordering                          kbo
% 3.16/0.98  --res_to_prop_solver                    active
% 3.16/0.98  --res_prop_simpl_new                    false
% 3.16/0.98  --res_prop_simpl_given                  true
% 3.16/0.98  --res_passive_queue_type                priority_queues
% 3.16/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.98  --res_passive_queues_freq               [15;5]
% 3.16/0.98  --res_forward_subs                      full
% 3.16/0.98  --res_backward_subs                     full
% 3.16/0.98  --res_forward_subs_resolution           true
% 3.16/0.98  --res_backward_subs_resolution          true
% 3.16/0.98  --res_orphan_elimination                true
% 3.16/0.98  --res_time_limit                        2.
% 3.16/0.98  --res_out_proof                         true
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Options
% 3.16/0.98  
% 3.16/0.98  --superposition_flag                    true
% 3.16/0.98  --sup_passive_queue_type                priority_queues
% 3.16/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.98  --demod_completeness_check              fast
% 3.16/0.98  --demod_use_ground                      true
% 3.16/0.98  --sup_to_prop_solver                    passive
% 3.16/0.98  --sup_prop_simpl_new                    true
% 3.16/0.98  --sup_prop_simpl_given                  true
% 3.16/0.98  --sup_fun_splitting                     false
% 3.16/0.98  --sup_smt_interval                      50000
% 3.16/0.98  
% 3.16/0.98  ------ Superposition Simplification Setup
% 3.16/0.98  
% 3.16/0.98  --sup_indices_passive                   []
% 3.16/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_full_bw                           [BwDemod]
% 3.16/0.98  --sup_immed_triv                        [TrivRules]
% 3.16/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_immed_bw_main                     []
% 3.16/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.98  
% 3.16/0.98  ------ Combination Options
% 3.16/0.98  
% 3.16/0.98  --comb_res_mult                         3
% 3.16/0.98  --comb_sup_mult                         2
% 3.16/0.98  --comb_inst_mult                        10
% 3.16/0.98  
% 3.16/0.98  ------ Debug Options
% 3.16/0.98  
% 3.16/0.98  --dbg_backtrace                         false
% 3.16/0.98  --dbg_dump_prop_clauses                 false
% 3.16/0.98  --dbg_dump_prop_clauses_file            -
% 3.16/0.98  --dbg_out_stat                          false
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  ------ Proving...
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  % SZS status Theorem for theBenchmark.p
% 3.16/0.98  
% 3.16/0.98   Resolution empty clause
% 3.16/0.98  
% 3.16/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/0.98  
% 3.16/0.98  fof(f14,axiom,(
% 3.16/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f29,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.16/0.98    inference(ennf_transformation,[],[f14])).
% 3.16/0.98  
% 3.16/0.98  fof(f30,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.16/0.98    inference(flattening,[],[f29])).
% 3.16/0.98  
% 3.16/0.98  fof(f72,plain,(
% 3.16/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f30])).
% 3.16/0.98  
% 3.16/0.98  fof(f11,axiom,(
% 3.16/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f25,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.16/0.98    inference(ennf_transformation,[],[f11])).
% 3.16/0.98  
% 3.16/0.98  fof(f26,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.98    inference(flattening,[],[f25])).
% 3.16/0.98  
% 3.16/0.98  fof(f44,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.98    inference(nnf_transformation,[],[f26])).
% 3.16/0.98  
% 3.16/0.98  fof(f66,plain,(
% 3.16/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f44])).
% 3.16/0.98  
% 3.16/0.98  fof(f18,conjecture,(
% 3.16/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f19,negated_conjecture,(
% 3.16/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.16/0.98    inference(negated_conjecture,[],[f18])).
% 3.16/0.98  
% 3.16/0.98  fof(f35,plain,(
% 3.16/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.16/0.98    inference(ennf_transformation,[],[f19])).
% 3.16/0.98  
% 3.16/0.98  fof(f36,plain,(
% 3.16/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.16/0.98    inference(flattening,[],[f35])).
% 3.16/0.98  
% 3.16/0.98  fof(f47,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.16/0.98    introduced(choice_axiom,[])).
% 3.16/0.98  
% 3.16/0.98  fof(f46,plain,(
% 3.16/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.16/0.98    introduced(choice_axiom,[])).
% 3.16/0.98  
% 3.16/0.98  fof(f48,plain,(
% 3.16/0.98    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.16/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f47,f46])).
% 3.16/0.98  
% 3.16/0.98  fof(f83,plain,(
% 3.16/0.98    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f12,axiom,(
% 3.16/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f68,plain,(
% 3.16/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f12])).
% 3.16/0.98  
% 3.16/0.98  fof(f15,axiom,(
% 3.16/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f73,plain,(
% 3.16/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f15])).
% 3.16/0.98  
% 3.16/0.98  fof(f88,plain,(
% 3.16/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.16/0.98    inference(definition_unfolding,[],[f68,f73])).
% 3.16/0.98  
% 3.16/0.98  fof(f77,plain,(
% 3.16/0.98    v1_funct_1(sK3)),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f79,plain,(
% 3.16/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f80,plain,(
% 3.16/0.98    v1_funct_1(sK4)),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f82,plain,(
% 3.16/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f5,axiom,(
% 3.16/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f43,plain,(
% 3.16/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.16/0.98    inference(nnf_transformation,[],[f5])).
% 3.16/0.98  
% 3.16/0.98  fof(f58,plain,(
% 3.16/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f43])).
% 3.16/0.98  
% 3.16/0.98  fof(f59,plain,(
% 3.16/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f43])).
% 3.16/0.98  
% 3.16/0.98  fof(f17,axiom,(
% 3.16/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f33,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.16/0.98    inference(ennf_transformation,[],[f17])).
% 3.16/0.98  
% 3.16/0.98  fof(f34,plain,(
% 3.16/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.16/0.98    inference(flattening,[],[f33])).
% 3.16/0.98  
% 3.16/0.98  fof(f75,plain,(
% 3.16/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f34])).
% 3.16/0.98  
% 3.16/0.98  fof(f78,plain,(
% 3.16/0.98    v1_funct_2(sK3,sK1,sK2)),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f81,plain,(
% 3.16/0.98    v1_funct_2(sK4,sK2,sK1)),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f10,axiom,(
% 3.16/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f24,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.98    inference(ennf_transformation,[],[f10])).
% 3.16/0.98  
% 3.16/0.98  fof(f65,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f24])).
% 3.16/0.98  
% 3.16/0.98  fof(f16,axiom,(
% 3.16/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f31,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.16/0.98    inference(ennf_transformation,[],[f16])).
% 3.16/0.98  
% 3.16/0.98  fof(f32,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.16/0.98    inference(flattening,[],[f31])).
% 3.16/0.98  
% 3.16/0.98  fof(f74,plain,(
% 3.16/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f32])).
% 3.16/0.98  
% 3.16/0.98  fof(f9,axiom,(
% 3.16/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f20,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.16/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.16/0.98  
% 3.16/0.98  fof(f23,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.98    inference(ennf_transformation,[],[f20])).
% 3.16/0.98  
% 3.16/0.98  fof(f64,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f23])).
% 3.16/0.98  
% 3.16/0.98  fof(f13,axiom,(
% 3.16/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f27,plain,(
% 3.16/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/0.98    inference(ennf_transformation,[],[f13])).
% 3.16/0.98  
% 3.16/0.98  fof(f28,plain,(
% 3.16/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/0.98    inference(flattening,[],[f27])).
% 3.16/0.98  
% 3.16/0.98  fof(f45,plain,(
% 3.16/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/0.98    inference(nnf_transformation,[],[f28])).
% 3.16/0.98  
% 3.16/0.98  fof(f70,plain,(
% 3.16/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f45])).
% 3.16/0.98  
% 3.16/0.98  fof(f94,plain,(
% 3.16/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.16/0.98    inference(equality_resolution,[],[f70])).
% 3.16/0.98  
% 3.16/0.98  fof(f8,axiom,(
% 3.16/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f22,plain,(
% 3.16/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.98    inference(ennf_transformation,[],[f8])).
% 3.16/0.98  
% 3.16/0.98  fof(f63,plain,(
% 3.16/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f22])).
% 3.16/0.98  
% 3.16/0.98  fof(f84,plain,(
% 3.16/0.98    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 3.16/0.98    inference(cnf_transformation,[],[f48])).
% 3.16/0.98  
% 3.16/0.98  fof(f7,axiom,(
% 3.16/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f62,plain,(
% 3.16/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f7])).
% 3.16/0.98  
% 3.16/0.98  fof(f86,plain,(
% 3.16/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.16/0.98    inference(definition_unfolding,[],[f62,f73])).
% 3.16/0.98  
% 3.16/0.98  fof(f2,axiom,(
% 3.16/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f37,plain,(
% 3.16/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.98    inference(nnf_transformation,[],[f2])).
% 3.16/0.98  
% 3.16/0.98  fof(f38,plain,(
% 3.16/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.98    inference(flattening,[],[f37])).
% 3.16/0.98  
% 3.16/0.98  fof(f52,plain,(
% 3.16/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f38])).
% 3.16/0.98  
% 3.16/0.98  fof(f3,axiom,(
% 3.16/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f39,plain,(
% 3.16/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.16/0.98    inference(nnf_transformation,[],[f3])).
% 3.16/0.98  
% 3.16/0.98  fof(f40,plain,(
% 3.16/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.16/0.98    inference(flattening,[],[f39])).
% 3.16/0.98  
% 3.16/0.98  fof(f54,plain,(
% 3.16/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.16/0.98    inference(cnf_transformation,[],[f40])).
% 3.16/0.98  
% 3.16/0.98  fof(f92,plain,(
% 3.16/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.16/0.98    inference(equality_resolution,[],[f54])).
% 3.16/0.98  
% 3.16/0.98  fof(f6,axiom,(
% 3.16/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f60,plain,(
% 3.16/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.16/0.98    inference(cnf_transformation,[],[f6])).
% 3.16/0.98  
% 3.16/0.98  fof(f85,plain,(
% 3.16/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.16/0.98    inference(definition_unfolding,[],[f60,f73])).
% 3.16/0.98  
% 3.16/0.98  fof(f53,plain,(
% 3.16/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f40])).
% 3.16/0.98  
% 3.16/0.98  fof(f4,axiom,(
% 3.16/0.98    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f41,plain,(
% 3.16/0.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 3.16/0.98    introduced(choice_axiom,[])).
% 3.16/0.98  
% 3.16/0.98  fof(f42,plain,(
% 3.16/0.98    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 3.16/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f41])).
% 3.16/0.98  
% 3.16/0.98  fof(f56,plain,(
% 3.16/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f42])).
% 3.16/0.98  
% 3.16/0.98  fof(f1,axiom,(
% 3.16/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.16/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.98  
% 3.16/0.98  fof(f21,plain,(
% 3.16/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.16/0.98    inference(ennf_transformation,[],[f1])).
% 3.16/0.98  
% 3.16/0.98  fof(f49,plain,(
% 3.16/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.16/0.98    inference(cnf_transformation,[],[f21])).
% 3.16/0.98  
% 3.16/0.98  fof(f57,plain,(
% 3.16/0.98    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 3.16/0.98    inference(cnf_transformation,[],[f42])).
% 3.16/0.98  
% 3.16/0.98  cnf(c_22,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.16/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | ~ v1_funct_1(X3) ),
% 3.16/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1428,plain,
% 3.16/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.16/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.16/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.16/0.98      | v1_funct_1(X0) != iProver_top
% 3.16/0.98      | v1_funct_1(X3) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_18,plain,
% 3.16/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.16/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | X3 = X2 ),
% 3.16/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_28,negated_conjecture,
% 3.16/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_530,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | X3 = X0
% 3.16/0.98      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 3.16/0.98      | k6_partfun1(sK1) != X3
% 3.16/0.98      | sK1 != X2
% 3.16/0.98      | sK1 != X1 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_531,plain,
% 3.16/0.98      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/0.98      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/0.98      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_530]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_19,plain,
% 3.16/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.16/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_539,plain,
% 3.16/0.98      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/0.98      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.16/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_531,c_19]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1415,plain,
% 3.16/0.98      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.16/0.98      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3741,plain,
% 3.16/0.98      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.16/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.16/0.98      | v1_funct_1(sK3) != iProver_top
% 3.16/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1428,c_1415]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_34,negated_conjecture,
% 3.16/0.98      ( v1_funct_1(sK3) ),
% 3.16/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_32,negated_conjecture,
% 3.16/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.16/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_31,negated_conjecture,
% 3.16/0.98      ( v1_funct_1(sK4) ),
% 3.16/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_29,negated_conjecture,
% 3.16/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.16/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_10,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2140,plain,
% 3.16/0.98      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/0.98      | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_9,plain,
% 3.16/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1433,plain,
% 3.16/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.16/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2580,plain,
% 3.16/0.98      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 3.16/0.98      | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1433,c_1415]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2597,plain,
% 3.16/0.98      ( ~ r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1))
% 3.16/0.98      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 3.16/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2580]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1754,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.16/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | ~ v1_funct_1(sK4) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1941,plain,
% 3.16/0.98      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 3.16/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.16/0.98      | ~ v1_funct_1(sK3)
% 3.16/0.98      | ~ v1_funct_1(sK4) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1754]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2356,plain,
% 3.16/0.98      ( m1_subset_1(k1_partfun1(sK1,sK2,X0,X1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.16/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.16/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | ~ v1_funct_1(sK3)
% 3.16/0.98      | ~ v1_funct_1(sK4) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1941]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3251,plain,
% 3.16/0.98      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.16/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.16/0.98      | ~ v1_funct_1(sK3)
% 3.16/0.98      | ~ v1_funct_1(sK4) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_2356]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4215,plain,
% 3.16/0.98      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_3741,c_34,c_32,c_31,c_29,c_2140,c_2597,c_3251]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_26,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | ~ v1_funct_2(X3,X4,X1)
% 3.16/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | ~ v1_funct_1(X3)
% 3.16/0.98      | v2_funct_1(X3)
% 3.16/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.16/0.98      | k1_xboole_0 = X2 ),
% 3.16/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1425,plain,
% 3.16/0.98      ( k1_xboole_0 = X0
% 3.16/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.16/0.98      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.16/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.16/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.16/0.98      | v1_funct_1(X1) != iProver_top
% 3.16/0.98      | v1_funct_1(X3) != iProver_top
% 3.16/0.98      | v2_funct_1(X3) = iProver_top
% 3.16/0.98      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4242,plain,
% 3.16/0.98      ( sK1 = k1_xboole_0
% 3.16/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.16/0.98      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.16/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.16/0.98      | v1_funct_1(sK3) != iProver_top
% 3.16/0.98      | v1_funct_1(sK4) != iProver_top
% 3.16/0.98      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.16/0.98      | v2_funct_1(sK3) = iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_4215,c_1425]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_35,plain,
% 3.16/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_33,negated_conjecture,
% 3.16/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.16/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_36,plain,
% 3.16/0.98      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_37,plain,
% 3.16/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_38,plain,
% 3.16/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_30,negated_conjecture,
% 3.16/0.98      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.16/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_39,plain,
% 3.16/0.98      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_40,plain,
% 3.16/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1424,plain,
% 3.16/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_16,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1430,plain,
% 3.16/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.16/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2859,plain,
% 3.16/0.98      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1424,c_1430]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_24,plain,
% 3.16/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.16/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.16/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.16/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.16/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.98      | ~ v1_funct_1(X2)
% 3.16/0.98      | ~ v1_funct_1(X3)
% 3.16/0.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.16/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_543,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.98      | ~ v1_funct_2(X3,X2,X1)
% 3.16/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | ~ v1_funct_1(X3)
% 3.16/0.98      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.16/0.98      | k2_relset_1(X1,X2,X0) = X2
% 3.16/0.98      | k6_partfun1(X2) != k6_partfun1(sK1)
% 3.16/0.98      | sK1 != X2 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_544,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,sK1)
% 3.16/0.98      | ~ v1_funct_2(X2,sK1,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.16/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | ~ v1_funct_1(X2)
% 3.16/0.98      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.16/0.98      | k2_relset_1(X1,sK1,X0) = sK1
% 3.16/0.98      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_543]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_620,plain,
% 3.16/0.98      ( ~ v1_funct_2(X0,X1,sK1)
% 3.16/0.98      | ~ v1_funct_2(X2,sK1,X1)
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.16/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.16/0.98      | ~ v1_funct_1(X0)
% 3.16/0.98      | ~ v1_funct_1(X2)
% 3.16/0.98      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.16/0.98      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 3.16/0.98      inference(equality_resolution_simp,[status(thm)],[c_544]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1414,plain,
% 3.16/0.98      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.16/0.98      | k2_relset_1(X0,sK1,X2) = sK1
% 3.16/0.98      | v1_funct_2(X2,X0,sK1) != iProver_top
% 3.16/0.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.16/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.16/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.16/0.98      | v1_funct_1(X2) != iProver_top
% 3.16/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2170,plain,
% 3.16/0.98      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 3.16/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.16/0.98      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.16/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.16/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.16/0.98      | v1_funct_1(sK3) != iProver_top
% 3.16/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.16/0.98      inference(equality_resolution,[status(thm)],[c_1414]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2227,plain,
% 3.16/0.98      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_2170,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2877,plain,
% 3.16/0.98      ( k2_relat_1(sK4) = sK1 ),
% 3.16/0.98      inference(light_normalisation,[status(thm)],[c_2859,c_2227]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_15,plain,
% 3.16/0.98      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.16/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_20,plain,
% 3.16/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/0.98      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.16/0.98      | ~ v1_relat_1(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_448,plain,
% 3.16/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.16/0.98      | ~ v1_relat_1(X0)
% 3.16/0.98      | X0 != X1
% 3.16/0.98      | k2_relat_1(X0) != X3 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_449,plain,
% 3.16/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.16/0.98      | ~ v1_relat_1(X0) ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_14,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.16/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_459,plain,
% 3.16/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.16/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_449,c_14]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_27,negated_conjecture,
% 3.16/0.98      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 3.16/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_474,plain,
% 3.16/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.16/0.98      | ~ v2_funct_1(sK3)
% 3.16/0.98      | k2_relat_1(X0) != sK1
% 3.16/0.98      | sK4 != X0 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_459,c_27]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_475,plain,
% 3.16/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.16/0.98      | ~ v2_funct_1(sK3)
% 3.16/0.98      | k2_relat_1(sK4) != sK1 ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_474]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_815,plain,
% 3.16/0.98      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 3.16/0.98      inference(splitting,
% 3.16/0.98                [splitting(split),new_symbols(definition,[])],
% 3.16/0.98                [c_475]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1417,plain,
% 3.16/0.98      ( k2_relat_1(sK4) != sK1
% 3.16/0.98      | v2_funct_1(sK3) != iProver_top
% 3.16/0.98      | sP0_iProver_split = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3274,plain,
% 3.16/0.98      ( sK1 != sK1
% 3.16/0.98      | v2_funct_1(sK3) != iProver_top
% 3.16/0.98      | sP0_iProver_split = iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_2877,c_1417]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3275,plain,
% 3.16/0.98      ( v2_funct_1(sK3) != iProver_top | sP0_iProver_split = iProver_top ),
% 3.16/0.98      inference(equality_resolution_simp,[status(thm)],[c_3274]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_814,plain,
% 3.16/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.16/0.98      | ~ sP0_iProver_split ),
% 3.16/0.98      inference(splitting,
% 3.16/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.16/0.98                [c_475]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1418,plain,
% 3.16/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
% 3.16/0.98      | sP0_iProver_split != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3273,plain,
% 3.16/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.16/0.98      | sP0_iProver_split != iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_2877,c_1418]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3406,plain,
% 3.16/0.98      ( sP0_iProver_split != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1424,c_3273]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4368,plain,
% 3.16/0.98      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top | sK1 = k1_xboole_0 ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_4242,c_35,c_36,c_37,c_38,c_39,c_40,c_3275,c_3406]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4369,plain,
% 3.16/0.98      ( sK1 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 3.16/0.98      inference(renaming,[status(thm)],[c_4368]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_12,plain,
% 3.16/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1431,plain,
% 3.16/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4374,plain,
% 3.16/0.98      ( sK1 = k1_xboole_0 ),
% 3.16/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_4369,c_1431]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1421,plain,
% 3.16/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1432,plain,
% 3.16/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.16/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2505,plain,
% 3.16/0.98      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1421,c_1432]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1,plain,
% 3.16/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.16/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1436,plain,
% 3.16/0.98      ( X0 = X1
% 3.16/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.16/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_3155,plain,
% 3.16/0.98      ( k2_zfmisc_1(sK1,sK2) = sK3
% 3.16/0.98      | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_2505,c_1436]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4378,plain,
% 3.16/0.98      ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3
% 3.16/0.98      | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_4374,c_3155]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_5,plain,
% 3.16/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.16/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4418,plain,
% 3.16/0.98      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_4378,c_5]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_85,plain,
% 3.16/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_87,plain,
% 3.16/0.98      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_85]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_11,plain,
% 3.16/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.16/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_6,plain,
% 3.16/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.16/0.98      | k1_xboole_0 = X0
% 3.16/0.98      | k1_xboole_0 = X1 ),
% 3.16/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_100,plain,
% 3.16/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.16/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_101,plain,
% 3.16/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_823,plain,
% 3.16/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.16/0.98      theory(equality) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1666,plain,
% 3.16/0.98      ( v2_funct_1(X0)
% 3.16/0.98      | ~ v2_funct_1(k6_partfun1(X1))
% 3.16/0.98      | X0 != k6_partfun1(X1) ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_823]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1667,plain,
% 3.16/0.98      ( X0 != k6_partfun1(X1)
% 3.16/0.98      | v2_funct_1(X0) = iProver_top
% 3.16/0.98      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_1666]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1669,plain,
% 3.16/0.98      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.16/0.98      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.16/0.98      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1667]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_818,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1911,plain,
% 3.16/0.98      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_818]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1912,plain,
% 3.16/0.98      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.16/0.98      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.16/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1911]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2084,plain,
% 3.16/0.98      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2085,plain,
% 3.16/0.98      ( sK3 = X0
% 3.16/0.98      | r1_tarski(X0,sK3) != iProver_top
% 3.16/0.98      | r1_tarski(sK3,X0) != iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_2084]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2087,plain,
% 3.16/0.98      ( sK3 = k1_xboole_0
% 3.16/0.98      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.16/0.98      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_2085]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2415,plain,
% 3.16/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_823]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2416,plain,
% 3.16/0.98      ( sK3 != X0
% 3.16/0.98      | v2_funct_1(X0) != iProver_top
% 3.16/0.98      | v2_funct_1(sK3) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_2415]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2418,plain,
% 3.16/0.98      ( sK3 != k1_xboole_0
% 3.16/0.98      | v2_funct_1(sK3) = iProver_top
% 3.16/0.98      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.16/0.98      inference(instantiation,[status(thm)],[c_2416]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4382,plain,
% 3.16/0.98      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_4374,c_2505]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_4405,plain,
% 3.16/0.98      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.16/0.98      inference(demodulation,[status(thm)],[c_4382,c_5]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_5364,plain,
% 3.16/0.98      ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.16/0.98      inference(global_propositional_subsumption,
% 3.16/0.98                [status(thm)],
% 3.16/0.98                [c_4418,c_87,c_11,c_100,c_101,c_1669,c_1912,c_2087,c_2418,
% 3.16/0.98                 c_3275,c_3406,c_4405]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_8,plain,
% 3.16/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1434,plain,
% 3.16/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.16/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_0,plain,
% 3.16/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.16/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_7,plain,
% 3.16/0.98      ( v1_xboole_0(sK0(X0)) ),
% 3.16/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_422,plain,
% 3.16/0.98      ( sK0(X0) != X1 | k1_xboole_0 = X1 ),
% 3.16/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_423,plain,
% 3.16/0.98      ( k1_xboole_0 = sK0(X0) ),
% 3.16/0.98      inference(unflattening,[status(thm)],[c_422]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_1457,plain,
% 3.16/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.16/0.98      inference(light_normalisation,[status(thm)],[c_1434,c_423]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_2506,plain,
% 3.16/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.16/0.98      inference(superposition,[status(thm)],[c_1457,c_1432]) ).
% 3.16/0.98  
% 3.16/0.98  cnf(c_5369,plain,
% 3.16/0.98      ( $false ),
% 3.16/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_5364,c_2506]) ).
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/0.98  
% 3.16/0.98  ------                               Statistics
% 3.16/0.98  
% 3.16/0.98  ------ General
% 3.16/0.98  
% 3.16/0.98  abstr_ref_over_cycles:                  0
% 3.16/0.98  abstr_ref_under_cycles:                 0
% 3.16/0.98  gc_basic_clause_elim:                   0
% 3.16/0.98  forced_gc_time:                         0
% 3.16/0.98  parsing_time:                           0.01
% 3.16/0.98  unif_index_cands_time:                  0.
% 3.16/0.98  unif_index_add_time:                    0.
% 3.16/0.98  orderings_time:                         0.
% 3.16/0.98  out_proof_time:                         0.01
% 3.16/0.98  total_time:                             0.207
% 3.16/0.98  num_of_symbols:                         54
% 3.16/0.98  num_of_terms:                           7933
% 3.16/0.98  
% 3.16/0.98  ------ Preprocessing
% 3.16/0.98  
% 3.16/0.98  num_of_splits:                          1
% 3.16/0.98  num_of_split_atoms:                     1
% 3.16/0.98  num_of_reused_defs:                     0
% 3.16/0.98  num_eq_ax_congr_red:                    18
% 3.16/0.98  num_of_sem_filtered_clauses:            1
% 3.16/0.98  num_of_subtypes:                        0
% 3.16/0.98  monotx_restored_types:                  0
% 3.16/0.98  sat_num_of_epr_types:                   0
% 3.16/0.98  sat_num_of_non_cyclic_types:            0
% 3.16/0.98  sat_guarded_non_collapsed_types:        0
% 3.16/0.98  num_pure_diseq_elim:                    0
% 3.16/0.98  simp_replaced_by:                       0
% 3.16/0.98  res_preprocessed:                       142
% 3.16/0.98  prep_upred:                             0
% 3.16/0.98  prep_unflattend:                        18
% 3.16/0.98  smt_new_axioms:                         0
% 3.16/0.98  pred_elim_cands:                        5
% 3.16/0.98  pred_elim:                              5
% 3.16/0.98  pred_elim_cl:                           7
% 3.16/0.98  pred_elim_cycles:                       7
% 3.16/0.98  merged_defs:                            8
% 3.16/0.98  merged_defs_ncl:                        0
% 3.16/0.98  bin_hyper_res:                          8
% 3.16/0.98  prep_cycles:                            4
% 3.16/0.98  pred_elim_time:                         0.005
% 3.16/0.98  splitting_time:                         0.
% 3.16/0.98  sem_filter_time:                        0.
% 3.16/0.98  monotx_time:                            0.001
% 3.16/0.98  subtype_inf_time:                       0.
% 3.16/0.98  
% 3.16/0.98  ------ Problem properties
% 3.16/0.98  
% 3.16/0.98  clauses:                                28
% 3.16/0.98  conjectures:                            6
% 3.16/0.98  epr:                                    6
% 3.16/0.98  horn:                                   26
% 3.16/0.98  ground:                                 9
% 3.16/0.98  unary:                                  14
% 3.16/0.98  binary:                                 5
% 3.16/0.98  lits:                                   76
% 3.16/0.98  lits_eq:                                16
% 3.16/0.98  fd_pure:                                0
% 3.16/0.98  fd_pseudo:                              0
% 3.16/0.98  fd_cond:                                2
% 3.16/0.98  fd_pseudo_cond:                         1
% 3.16/0.98  ac_symbols:                             0
% 3.16/0.98  
% 3.16/0.98  ------ Propositional Solver
% 3.16/0.98  
% 3.16/0.98  prop_solver_calls:                      27
% 3.16/0.98  prop_fast_solver_calls:                 988
% 3.16/0.98  smt_solver_calls:                       0
% 3.16/0.98  smt_fast_solver_calls:                  0
% 3.16/0.98  prop_num_of_clauses:                    2138
% 3.16/0.98  prop_preprocess_simplified:             5888
% 3.16/0.98  prop_fo_subsumed:                       24
% 3.16/0.98  prop_solver_time:                       0.
% 3.16/0.98  smt_solver_time:                        0.
% 3.16/0.98  smt_fast_solver_time:                   0.
% 3.16/0.98  prop_fast_solver_time:                  0.
% 3.16/0.98  prop_unsat_core_time:                   0.
% 3.16/0.98  
% 3.16/0.98  ------ QBF
% 3.16/0.98  
% 3.16/0.98  qbf_q_res:                              0
% 3.16/0.98  qbf_num_tautologies:                    0
% 3.16/0.98  qbf_prep_cycles:                        0
% 3.16/0.98  
% 3.16/0.98  ------ BMC1
% 3.16/0.98  
% 3.16/0.98  bmc1_current_bound:                     -1
% 3.16/0.98  bmc1_last_solved_bound:                 -1
% 3.16/0.98  bmc1_unsat_core_size:                   -1
% 3.16/0.98  bmc1_unsat_core_parents_size:           -1
% 3.16/0.98  bmc1_merge_next_fun:                    0
% 3.16/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.16/0.98  
% 3.16/0.98  ------ Instantiation
% 3.16/0.98  
% 3.16/0.98  inst_num_of_clauses:                    697
% 3.16/0.98  inst_num_in_passive:                    13
% 3.16/0.98  inst_num_in_active:                     347
% 3.16/0.98  inst_num_in_unprocessed:                340
% 3.16/0.98  inst_num_of_loops:                      360
% 3.16/0.98  inst_num_of_learning_restarts:          0
% 3.16/0.98  inst_num_moves_active_passive:          10
% 3.16/0.98  inst_lit_activity:                      0
% 3.16/0.98  inst_lit_activity_moves:                0
% 3.16/0.98  inst_num_tautologies:                   0
% 3.16/0.98  inst_num_prop_implied:                  0
% 3.16/0.98  inst_num_existing_simplified:           0
% 3.16/0.98  inst_num_eq_res_simplified:             0
% 3.16/0.98  inst_num_child_elim:                    0
% 3.16/0.98  inst_num_of_dismatching_blockings:      156
% 3.16/0.98  inst_num_of_non_proper_insts:           626
% 3.16/0.98  inst_num_of_duplicates:                 0
% 3.16/0.98  inst_inst_num_from_inst_to_res:         0
% 3.16/0.98  inst_dismatching_checking_time:         0.
% 3.16/0.98  
% 3.16/0.98  ------ Resolution
% 3.16/0.98  
% 3.16/0.98  res_num_of_clauses:                     0
% 3.16/0.98  res_num_in_passive:                     0
% 3.16/0.98  res_num_in_active:                      0
% 3.16/0.98  res_num_of_loops:                       146
% 3.16/0.98  res_forward_subset_subsumed:            32
% 3.16/0.98  res_backward_subset_subsumed:           6
% 3.16/0.98  res_forward_subsumed:                   0
% 3.16/0.98  res_backward_subsumed:                  0
% 3.16/0.98  res_forward_subsumption_resolution:     4
% 3.16/0.98  res_backward_subsumption_resolution:    0
% 3.16/0.98  res_clause_to_clause_subsumption:       263
% 3.16/0.98  res_orphan_elimination:                 0
% 3.16/0.98  res_tautology_del:                      36
% 3.16/0.98  res_num_eq_res_simplified:              1
% 3.16/0.98  res_num_sel_changes:                    0
% 3.16/0.98  res_moves_from_active_to_pass:          0
% 3.16/0.98  
% 3.16/0.98  ------ Superposition
% 3.16/0.98  
% 3.16/0.98  sup_time_total:                         0.
% 3.16/0.98  sup_time_generating:                    0.
% 3.16/0.98  sup_time_sim_full:                      0.
% 3.16/0.98  sup_time_sim_immed:                     0.
% 3.16/0.98  
% 3.16/0.98  sup_num_of_clauses:                     63
% 3.16/0.98  sup_num_in_active:                      40
% 3.16/0.98  sup_num_in_passive:                     23
% 3.16/0.98  sup_num_of_loops:                       71
% 3.16/0.98  sup_fw_superposition:                   42
% 3.16/0.98  sup_bw_superposition:                   34
% 3.16/0.98  sup_immediate_simplified:               27
% 3.16/0.98  sup_given_eliminated:                   1
% 3.16/0.98  comparisons_done:                       0
% 3.16/0.98  comparisons_avoided:                    0
% 3.16/0.98  
% 3.16/0.98  ------ Simplifications
% 3.16/0.98  
% 3.16/0.98  
% 3.16/0.98  sim_fw_subset_subsumed:                 4
% 3.16/0.98  sim_bw_subset_subsumed:                 1
% 3.16/0.98  sim_fw_subsumed:                        12
% 3.16/0.98  sim_bw_subsumed:                        1
% 3.16/0.98  sim_fw_subsumption_res:                 3
% 3.16/0.98  sim_bw_subsumption_res:                 0
% 3.16/0.98  sim_tautology_del:                      1
% 3.16/0.98  sim_eq_tautology_del:                   4
% 3.16/0.98  sim_eq_res_simp:                        1
% 3.16/0.98  sim_fw_demodulated:                     14
% 3.16/0.98  sim_bw_demodulated:                     29
% 3.16/0.98  sim_light_normalised:                   10
% 3.16/0.98  sim_joinable_taut:                      0
% 3.16/0.98  sim_joinable_simp:                      0
% 3.16/0.98  sim_ac_normalised:                      0
% 3.16/0.98  sim_smt_subsumption:                    0
% 3.16/0.98  
%------------------------------------------------------------------------------
