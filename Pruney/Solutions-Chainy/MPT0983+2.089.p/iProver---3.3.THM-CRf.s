%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:03 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 778 expanded)
%              Number of clauses        :   94 ( 237 expanded)
%              Number of leaves         :   23 ( 192 expanded)
%              Depth                    :   21
%              Number of atoms          :  581 (4922 expanded)
%              Number of equality atoms :  212 ( 447 expanded)
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

fof(f69,plain,(
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

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f47,f46])).

fof(f80,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f72,plain,(
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

fof(f75,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f62,plain,(
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

fof(f71,plain,(
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

fof(f61,plain,(
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f70])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1056,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_439,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_447,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_439,c_16])).

cnf(c_1042,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_2716,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1042])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2980,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2716,c_32,c_34,c_35,c_37])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1053,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3667,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2980,c_1053])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1052,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1058,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2183,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1052,c_1058])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_451,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_526,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_452])).

cnf(c_1041,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_1843,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1041])).

cnf(c_1890,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1843,c_32,c_33,c_34,c_35,c_36,c_37])).

cnf(c_2198,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2183,c_1890])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_356,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_357,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_367,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_357,c_11])).

cnf(c_24,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_367,c_24])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_646,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_383])).

cnf(c_1044,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_2339,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2198,c_1044])).

cnf(c_2340,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2339])).

cnf(c_645,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_383])).

cnf(c_1045,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_2338,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2198,c_1045])).

cnf(c_2356,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1052,c_2338])).

cnf(c_9098,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3667,c_32,c_33,c_34,c_35,c_36,c_37,c_2340,c_2356])).

cnf(c_9099,plain,
    ( sK1 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9098])).

cnf(c_9,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1059,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9104,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9099,c_1059])).

cnf(c_1049,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9158,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9104,c_1049])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_9166,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9158,c_5])).

cnf(c_655,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2093,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_2094,plain,
    ( sK3 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2093])).

cnf(c_2096,plain,
    ( sK3 != k1_xboole_0
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2094])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1767,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1768,plain,
    ( sK3 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1767])).

cnf(c_1770,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_1644,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_1645,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_1647,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1645])).

cnf(c_649,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1548,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1549,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_1272,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_1273,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_1275,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_93,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9166,c_2356,c_2340,c_2096,c_1770,c_1647,c_1549,c_1275,c_93,c_89,c_88,c_8,c_84])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.65/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.01  
% 3.65/1.01  ------  iProver source info
% 3.65/1.01  
% 3.65/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.01  git: non_committed_changes: false
% 3.65/1.01  git: last_make_outside_of_git: false
% 3.65/1.01  
% 3.65/1.01  ------ 
% 3.65/1.01  
% 3.65/1.01  ------ Input Options
% 3.65/1.01  
% 3.65/1.01  --out_options                           all
% 3.65/1.01  --tptp_safe_out                         true
% 3.65/1.01  --problem_path                          ""
% 3.65/1.01  --include_path                          ""
% 3.65/1.01  --clausifier                            res/vclausify_rel
% 3.65/1.01  --clausifier_options                    --mode clausify
% 3.65/1.01  --stdin                                 false
% 3.65/1.01  --stats_out                             all
% 3.65/1.01  
% 3.65/1.01  ------ General Options
% 3.65/1.01  
% 3.65/1.01  --fof                                   false
% 3.65/1.01  --time_out_real                         305.
% 3.65/1.01  --time_out_virtual                      -1.
% 3.65/1.01  --symbol_type_check                     false
% 3.65/1.01  --clausify_out                          false
% 3.65/1.01  --sig_cnt_out                           false
% 3.65/1.01  --trig_cnt_out                          false
% 3.65/1.01  --trig_cnt_out_tolerance                1.
% 3.65/1.01  --trig_cnt_out_sk_spl                   false
% 3.65/1.01  --abstr_cl_out                          false
% 3.65/1.01  
% 3.65/1.01  ------ Global Options
% 3.65/1.01  
% 3.65/1.01  --schedule                              default
% 3.65/1.01  --add_important_lit                     false
% 3.65/1.01  --prop_solver_per_cl                    1000
% 3.65/1.01  --min_unsat_core                        false
% 3.65/1.01  --soft_assumptions                      false
% 3.65/1.01  --soft_lemma_size                       3
% 3.65/1.01  --prop_impl_unit_size                   0
% 3.65/1.01  --prop_impl_unit                        []
% 3.65/1.01  --share_sel_clauses                     true
% 3.65/1.01  --reset_solvers                         false
% 3.65/1.01  --bc_imp_inh                            [conj_cone]
% 3.65/1.01  --conj_cone_tolerance                   3.
% 3.65/1.01  --extra_neg_conj                        none
% 3.65/1.01  --large_theory_mode                     true
% 3.65/1.01  --prolific_symb_bound                   200
% 3.65/1.01  --lt_threshold                          2000
% 3.65/1.01  --clause_weak_htbl                      true
% 3.65/1.01  --gc_record_bc_elim                     false
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing Options
% 3.65/1.01  
% 3.65/1.01  --preprocessing_flag                    true
% 3.65/1.01  --time_out_prep_mult                    0.1
% 3.65/1.01  --splitting_mode                        input
% 3.65/1.01  --splitting_grd                         true
% 3.65/1.01  --splitting_cvd                         false
% 3.65/1.01  --splitting_cvd_svl                     false
% 3.65/1.01  --splitting_nvd                         32
% 3.65/1.01  --sub_typing                            true
% 3.65/1.01  --prep_gs_sim                           true
% 3.65/1.01  --prep_unflatten                        true
% 3.65/1.01  --prep_res_sim                          true
% 3.65/1.01  --prep_upred                            true
% 3.65/1.01  --prep_sem_filter                       exhaustive
% 3.65/1.01  --prep_sem_filter_out                   false
% 3.65/1.01  --pred_elim                             true
% 3.65/1.01  --res_sim_input                         true
% 3.65/1.01  --eq_ax_congr_red                       true
% 3.65/1.01  --pure_diseq_elim                       true
% 3.65/1.01  --brand_transform                       false
% 3.65/1.01  --non_eq_to_eq                          false
% 3.65/1.01  --prep_def_merge                        true
% 3.65/1.01  --prep_def_merge_prop_impl              false
% 3.65/1.01  --prep_def_merge_mbd                    true
% 3.65/1.01  --prep_def_merge_tr_red                 false
% 3.65/1.01  --prep_def_merge_tr_cl                  false
% 3.65/1.01  --smt_preprocessing                     true
% 3.65/1.01  --smt_ac_axioms                         fast
% 3.65/1.01  --preprocessed_out                      false
% 3.65/1.01  --preprocessed_stats                    false
% 3.65/1.01  
% 3.65/1.01  ------ Abstraction refinement Options
% 3.65/1.01  
% 3.65/1.01  --abstr_ref                             []
% 3.65/1.01  --abstr_ref_prep                        false
% 3.65/1.01  --abstr_ref_until_sat                   false
% 3.65/1.01  --abstr_ref_sig_restrict                funpre
% 3.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.01  --abstr_ref_under                       []
% 3.65/1.01  
% 3.65/1.01  ------ SAT Options
% 3.65/1.01  
% 3.65/1.01  --sat_mode                              false
% 3.65/1.01  --sat_fm_restart_options                ""
% 3.65/1.01  --sat_gr_def                            false
% 3.65/1.01  --sat_epr_types                         true
% 3.65/1.01  --sat_non_cyclic_types                  false
% 3.65/1.01  --sat_finite_models                     false
% 3.65/1.01  --sat_fm_lemmas                         false
% 3.65/1.01  --sat_fm_prep                           false
% 3.65/1.01  --sat_fm_uc_incr                        true
% 3.65/1.01  --sat_out_model                         small
% 3.65/1.01  --sat_out_clauses                       false
% 3.65/1.01  
% 3.65/1.01  ------ QBF Options
% 3.65/1.01  
% 3.65/1.01  --qbf_mode                              false
% 3.65/1.01  --qbf_elim_univ                         false
% 3.65/1.01  --qbf_dom_inst                          none
% 3.65/1.01  --qbf_dom_pre_inst                      false
% 3.65/1.01  --qbf_sk_in                             false
% 3.65/1.01  --qbf_pred_elim                         true
% 3.65/1.01  --qbf_split                             512
% 3.65/1.01  
% 3.65/1.01  ------ BMC1 Options
% 3.65/1.01  
% 3.65/1.01  --bmc1_incremental                      false
% 3.65/1.01  --bmc1_axioms                           reachable_all
% 3.65/1.01  --bmc1_min_bound                        0
% 3.65/1.01  --bmc1_max_bound                        -1
% 3.65/1.01  --bmc1_max_bound_default                -1
% 3.65/1.01  --bmc1_symbol_reachability              true
% 3.65/1.01  --bmc1_property_lemmas                  false
% 3.65/1.01  --bmc1_k_induction                      false
% 3.65/1.01  --bmc1_non_equiv_states                 false
% 3.65/1.01  --bmc1_deadlock                         false
% 3.65/1.01  --bmc1_ucm                              false
% 3.65/1.01  --bmc1_add_unsat_core                   none
% 3.65/1.01  --bmc1_unsat_core_children              false
% 3.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.01  --bmc1_out_stat                         full
% 3.65/1.01  --bmc1_ground_init                      false
% 3.65/1.01  --bmc1_pre_inst_next_state              false
% 3.65/1.01  --bmc1_pre_inst_state                   false
% 3.65/1.01  --bmc1_pre_inst_reach_state             false
% 3.65/1.01  --bmc1_out_unsat_core                   false
% 3.65/1.01  --bmc1_aig_witness_out                  false
% 3.65/1.01  --bmc1_verbose                          false
% 3.65/1.01  --bmc1_dump_clauses_tptp                false
% 3.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.01  --bmc1_dump_file                        -
% 3.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.01  --bmc1_ucm_extend_mode                  1
% 3.65/1.01  --bmc1_ucm_init_mode                    2
% 3.65/1.01  --bmc1_ucm_cone_mode                    none
% 3.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.01  --bmc1_ucm_relax_model                  4
% 3.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.01  --bmc1_ucm_layered_model                none
% 3.65/1.01  --bmc1_ucm_max_lemma_size               10
% 3.65/1.01  
% 3.65/1.01  ------ AIG Options
% 3.65/1.01  
% 3.65/1.01  --aig_mode                              false
% 3.65/1.01  
% 3.65/1.01  ------ Instantiation Options
% 3.65/1.01  
% 3.65/1.01  --instantiation_flag                    true
% 3.65/1.01  --inst_sos_flag                         false
% 3.65/1.01  --inst_sos_phase                        true
% 3.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel_side                     num_symb
% 3.65/1.01  --inst_solver_per_active                1400
% 3.65/1.01  --inst_solver_calls_frac                1.
% 3.65/1.01  --inst_passive_queue_type               priority_queues
% 3.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.01  --inst_passive_queues_freq              [25;2]
% 3.65/1.01  --inst_dismatching                      true
% 3.65/1.01  --inst_eager_unprocessed_to_passive     true
% 3.65/1.01  --inst_prop_sim_given                   true
% 3.65/1.01  --inst_prop_sim_new                     false
% 3.65/1.01  --inst_subs_new                         false
% 3.65/1.01  --inst_eq_res_simp                      false
% 3.65/1.01  --inst_subs_given                       false
% 3.65/1.01  --inst_orphan_elimination               true
% 3.65/1.01  --inst_learning_loop_flag               true
% 3.65/1.01  --inst_learning_start                   3000
% 3.65/1.01  --inst_learning_factor                  2
% 3.65/1.01  --inst_start_prop_sim_after_learn       3
% 3.65/1.01  --inst_sel_renew                        solver
% 3.65/1.01  --inst_lit_activity_flag                true
% 3.65/1.01  --inst_restr_to_given                   false
% 3.65/1.01  --inst_activity_threshold               500
% 3.65/1.01  --inst_out_proof                        true
% 3.65/1.01  
% 3.65/1.01  ------ Resolution Options
% 3.65/1.01  
% 3.65/1.01  --resolution_flag                       true
% 3.65/1.01  --res_lit_sel                           adaptive
% 3.65/1.01  --res_lit_sel_side                      none
% 3.65/1.01  --res_ordering                          kbo
% 3.65/1.01  --res_to_prop_solver                    active
% 3.65/1.01  --res_prop_simpl_new                    false
% 3.65/1.01  --res_prop_simpl_given                  true
% 3.65/1.01  --res_passive_queue_type                priority_queues
% 3.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.01  --res_passive_queues_freq               [15;5]
% 3.65/1.01  --res_forward_subs                      full
% 3.65/1.01  --res_backward_subs                     full
% 3.65/1.01  --res_forward_subs_resolution           true
% 3.65/1.01  --res_backward_subs_resolution          true
% 3.65/1.01  --res_orphan_elimination                true
% 3.65/1.01  --res_time_limit                        2.
% 3.65/1.01  --res_out_proof                         true
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Options
% 3.65/1.01  
% 3.65/1.01  --superposition_flag                    true
% 3.65/1.01  --sup_passive_queue_type                priority_queues
% 3.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.01  --demod_completeness_check              fast
% 3.65/1.01  --demod_use_ground                      true
% 3.65/1.01  --sup_to_prop_solver                    passive
% 3.65/1.01  --sup_prop_simpl_new                    true
% 3.65/1.01  --sup_prop_simpl_given                  true
% 3.65/1.01  --sup_fun_splitting                     false
% 3.65/1.01  --sup_smt_interval                      50000
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Simplification Setup
% 3.65/1.01  
% 3.65/1.01  --sup_indices_passive                   []
% 3.65/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.01  --sup_full_bw                           [BwDemod]
% 3.65/1.01  --sup_immed_triv                        [TrivRules]
% 3.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.01  --sup_immed_bw_main                     []
% 3.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.01  
% 3.65/1.01  ------ Combination Options
% 3.65/1.01  
% 3.65/1.01  --comb_res_mult                         3
% 3.65/1.01  --comb_sup_mult                         2
% 3.65/1.01  --comb_inst_mult                        10
% 3.65/1.01  
% 3.65/1.01  ------ Debug Options
% 3.65/1.01  
% 3.65/1.01  --dbg_backtrace                         false
% 3.65/1.01  --dbg_dump_prop_clauses                 false
% 3.65/1.01  --dbg_dump_prop_clauses_file            -
% 3.65/1.01  --dbg_out_stat                          false
% 3.65/1.01  ------ Parsing...
% 3.65/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.01  ------ Proving...
% 3.65/1.01  ------ Problem Properties 
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  clauses                                 25
% 3.65/1.01  conjectures                             6
% 3.65/1.01  EPR                                     6
% 3.65/1.01  Horn                                    23
% 3.65/1.01  unary                                   12
% 3.65/1.01  binary                                  3
% 3.65/1.01  lits                                    73
% 3.65/1.01  lits eq                                 15
% 3.65/1.01  fd_pure                                 0
% 3.65/1.01  fd_pseudo                               0
% 3.65/1.01  fd_cond                                 2
% 3.65/1.01  fd_pseudo_cond                          1
% 3.65/1.01  AC symbols                              0
% 3.65/1.01  
% 3.65/1.01  ------ Schedule dynamic 5 is on 
% 3.65/1.01  
% 3.65/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  ------ 
% 3.65/1.01  Current options:
% 3.65/1.01  ------ 
% 3.65/1.01  
% 3.65/1.01  ------ Input Options
% 3.65/1.01  
% 3.65/1.01  --out_options                           all
% 3.65/1.01  --tptp_safe_out                         true
% 3.65/1.01  --problem_path                          ""
% 3.65/1.01  --include_path                          ""
% 3.65/1.01  --clausifier                            res/vclausify_rel
% 3.65/1.01  --clausifier_options                    --mode clausify
% 3.65/1.01  --stdin                                 false
% 3.65/1.01  --stats_out                             all
% 3.65/1.01  
% 3.65/1.01  ------ General Options
% 3.65/1.01  
% 3.65/1.01  --fof                                   false
% 3.65/1.01  --time_out_real                         305.
% 3.65/1.01  --time_out_virtual                      -1.
% 3.65/1.01  --symbol_type_check                     false
% 3.65/1.01  --clausify_out                          false
% 3.65/1.01  --sig_cnt_out                           false
% 3.65/1.01  --trig_cnt_out                          false
% 3.65/1.01  --trig_cnt_out_tolerance                1.
% 3.65/1.01  --trig_cnt_out_sk_spl                   false
% 3.65/1.01  --abstr_cl_out                          false
% 3.65/1.01  
% 3.65/1.01  ------ Global Options
% 3.65/1.01  
% 3.65/1.01  --schedule                              default
% 3.65/1.01  --add_important_lit                     false
% 3.65/1.01  --prop_solver_per_cl                    1000
% 3.65/1.01  --min_unsat_core                        false
% 3.65/1.01  --soft_assumptions                      false
% 3.65/1.01  --soft_lemma_size                       3
% 3.65/1.01  --prop_impl_unit_size                   0
% 3.65/1.01  --prop_impl_unit                        []
% 3.65/1.01  --share_sel_clauses                     true
% 3.65/1.01  --reset_solvers                         false
% 3.65/1.01  --bc_imp_inh                            [conj_cone]
% 3.65/1.01  --conj_cone_tolerance                   3.
% 3.65/1.01  --extra_neg_conj                        none
% 3.65/1.01  --large_theory_mode                     true
% 3.65/1.01  --prolific_symb_bound                   200
% 3.65/1.01  --lt_threshold                          2000
% 3.65/1.01  --clause_weak_htbl                      true
% 3.65/1.01  --gc_record_bc_elim                     false
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing Options
% 3.65/1.01  
% 3.65/1.01  --preprocessing_flag                    true
% 3.65/1.01  --time_out_prep_mult                    0.1
% 3.65/1.01  --splitting_mode                        input
% 3.65/1.01  --splitting_grd                         true
% 3.65/1.01  --splitting_cvd                         false
% 3.65/1.01  --splitting_cvd_svl                     false
% 3.65/1.01  --splitting_nvd                         32
% 3.65/1.01  --sub_typing                            true
% 3.65/1.01  --prep_gs_sim                           true
% 3.65/1.01  --prep_unflatten                        true
% 3.65/1.01  --prep_res_sim                          true
% 3.65/1.01  --prep_upred                            true
% 3.65/1.01  --prep_sem_filter                       exhaustive
% 3.65/1.01  --prep_sem_filter_out                   false
% 3.65/1.01  --pred_elim                             true
% 3.65/1.01  --res_sim_input                         true
% 3.65/1.01  --eq_ax_congr_red                       true
% 3.65/1.01  --pure_diseq_elim                       true
% 3.65/1.01  --brand_transform                       false
% 3.65/1.01  --non_eq_to_eq                          false
% 3.65/1.01  --prep_def_merge                        true
% 3.65/1.01  --prep_def_merge_prop_impl              false
% 3.65/1.01  --prep_def_merge_mbd                    true
% 3.65/1.01  --prep_def_merge_tr_red                 false
% 3.65/1.01  --prep_def_merge_tr_cl                  false
% 3.65/1.01  --smt_preprocessing                     true
% 3.65/1.01  --smt_ac_axioms                         fast
% 3.65/1.01  --preprocessed_out                      false
% 3.65/1.01  --preprocessed_stats                    false
% 3.65/1.01  
% 3.65/1.01  ------ Abstraction refinement Options
% 3.65/1.01  
% 3.65/1.01  --abstr_ref                             []
% 3.65/1.01  --abstr_ref_prep                        false
% 3.65/1.01  --abstr_ref_until_sat                   false
% 3.65/1.01  --abstr_ref_sig_restrict                funpre
% 3.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.01  --abstr_ref_under                       []
% 3.65/1.01  
% 3.65/1.01  ------ SAT Options
% 3.65/1.01  
% 3.65/1.01  --sat_mode                              false
% 3.65/1.01  --sat_fm_restart_options                ""
% 3.65/1.01  --sat_gr_def                            false
% 3.65/1.01  --sat_epr_types                         true
% 3.65/1.01  --sat_non_cyclic_types                  false
% 3.65/1.01  --sat_finite_models                     false
% 3.65/1.01  --sat_fm_lemmas                         false
% 3.65/1.01  --sat_fm_prep                           false
% 3.65/1.01  --sat_fm_uc_incr                        true
% 3.65/1.01  --sat_out_model                         small
% 3.65/1.01  --sat_out_clauses                       false
% 3.65/1.01  
% 3.65/1.01  ------ QBF Options
% 3.65/1.01  
% 3.65/1.01  --qbf_mode                              false
% 3.65/1.01  --qbf_elim_univ                         false
% 3.65/1.01  --qbf_dom_inst                          none
% 3.65/1.01  --qbf_dom_pre_inst                      false
% 3.65/1.01  --qbf_sk_in                             false
% 3.65/1.01  --qbf_pred_elim                         true
% 3.65/1.01  --qbf_split                             512
% 3.65/1.01  
% 3.65/1.01  ------ BMC1 Options
% 3.65/1.01  
% 3.65/1.01  --bmc1_incremental                      false
% 3.65/1.01  --bmc1_axioms                           reachable_all
% 3.65/1.01  --bmc1_min_bound                        0
% 3.65/1.01  --bmc1_max_bound                        -1
% 3.65/1.01  --bmc1_max_bound_default                -1
% 3.65/1.01  --bmc1_symbol_reachability              true
% 3.65/1.01  --bmc1_property_lemmas                  false
% 3.65/1.01  --bmc1_k_induction                      false
% 3.65/1.01  --bmc1_non_equiv_states                 false
% 3.65/1.01  --bmc1_deadlock                         false
% 3.65/1.01  --bmc1_ucm                              false
% 3.65/1.01  --bmc1_add_unsat_core                   none
% 3.65/1.01  --bmc1_unsat_core_children              false
% 3.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.01  --bmc1_out_stat                         full
% 3.65/1.01  --bmc1_ground_init                      false
% 3.65/1.01  --bmc1_pre_inst_next_state              false
% 3.65/1.01  --bmc1_pre_inst_state                   false
% 3.65/1.01  --bmc1_pre_inst_reach_state             false
% 3.65/1.01  --bmc1_out_unsat_core                   false
% 3.65/1.01  --bmc1_aig_witness_out                  false
% 3.65/1.01  --bmc1_verbose                          false
% 3.65/1.01  --bmc1_dump_clauses_tptp                false
% 3.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.01  --bmc1_dump_file                        -
% 3.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.01  --bmc1_ucm_extend_mode                  1
% 3.65/1.01  --bmc1_ucm_init_mode                    2
% 3.65/1.01  --bmc1_ucm_cone_mode                    none
% 3.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.01  --bmc1_ucm_relax_model                  4
% 3.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.01  --bmc1_ucm_layered_model                none
% 3.65/1.01  --bmc1_ucm_max_lemma_size               10
% 3.65/1.01  
% 3.65/1.01  ------ AIG Options
% 3.65/1.01  
% 3.65/1.01  --aig_mode                              false
% 3.65/1.01  
% 3.65/1.01  ------ Instantiation Options
% 3.65/1.01  
% 3.65/1.01  --instantiation_flag                    true
% 3.65/1.01  --inst_sos_flag                         false
% 3.65/1.01  --inst_sos_phase                        true
% 3.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel_side                     none
% 3.65/1.01  --inst_solver_per_active                1400
% 3.65/1.01  --inst_solver_calls_frac                1.
% 3.65/1.01  --inst_passive_queue_type               priority_queues
% 3.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.01  --inst_passive_queues_freq              [25;2]
% 3.65/1.01  --inst_dismatching                      true
% 3.65/1.01  --inst_eager_unprocessed_to_passive     true
% 3.65/1.01  --inst_prop_sim_given                   true
% 3.65/1.01  --inst_prop_sim_new                     false
% 3.65/1.01  --inst_subs_new                         false
% 3.65/1.01  --inst_eq_res_simp                      false
% 3.65/1.01  --inst_subs_given                       false
% 3.65/1.01  --inst_orphan_elimination               true
% 3.65/1.01  --inst_learning_loop_flag               true
% 3.65/1.01  --inst_learning_start                   3000
% 3.65/1.01  --inst_learning_factor                  2
% 3.65/1.01  --inst_start_prop_sim_after_learn       3
% 3.65/1.01  --inst_sel_renew                        solver
% 3.65/1.01  --inst_lit_activity_flag                true
% 3.65/1.01  --inst_restr_to_given                   false
% 3.65/1.01  --inst_activity_threshold               500
% 3.65/1.01  --inst_out_proof                        true
% 3.65/1.01  
% 3.65/1.01  ------ Resolution Options
% 3.65/1.01  
% 3.65/1.01  --resolution_flag                       false
% 3.65/1.01  --res_lit_sel                           adaptive
% 3.65/1.01  --res_lit_sel_side                      none
% 3.65/1.01  --res_ordering                          kbo
% 3.65/1.01  --res_to_prop_solver                    active
% 3.65/1.01  --res_prop_simpl_new                    false
% 3.65/1.01  --res_prop_simpl_given                  true
% 3.65/1.01  --res_passive_queue_type                priority_queues
% 3.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.01  --res_passive_queues_freq               [15;5]
% 3.65/1.01  --res_forward_subs                      full
% 3.65/1.01  --res_backward_subs                     full
% 3.65/1.01  --res_forward_subs_resolution           true
% 3.65/1.01  --res_backward_subs_resolution          true
% 3.65/1.01  --res_orphan_elimination                true
% 3.65/1.01  --res_time_limit                        2.
% 3.65/1.01  --res_out_proof                         true
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Options
% 3.65/1.01  
% 3.65/1.01  --superposition_flag                    true
% 3.65/1.01  --sup_passive_queue_type                priority_queues
% 3.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.01  --demod_completeness_check              fast
% 3.65/1.01  --demod_use_ground                      true
% 3.65/1.01  --sup_to_prop_solver                    passive
% 3.65/1.01  --sup_prop_simpl_new                    true
% 3.65/1.01  --sup_prop_simpl_given                  true
% 3.65/1.01  --sup_fun_splitting                     false
% 3.65/1.01  --sup_smt_interval                      50000
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Simplification Setup
% 3.65/1.01  
% 3.65/1.01  --sup_indices_passive                   []
% 3.65/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.01  --sup_full_bw                           [BwDemod]
% 3.65/1.01  --sup_immed_triv                        [TrivRules]
% 3.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.01  --sup_immed_bw_main                     []
% 3.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.01  
% 3.65/1.01  ------ Combination Options
% 3.65/1.01  
% 3.65/1.01  --comb_res_mult                         3
% 3.65/1.01  --comb_sup_mult                         2
% 3.65/1.01  --comb_inst_mult                        10
% 3.65/1.01  
% 3.65/1.01  ------ Debug Options
% 3.65/1.01  
% 3.65/1.01  --dbg_backtrace                         false
% 3.65/1.01  --dbg_dump_prop_clauses                 false
% 3.65/1.01  --dbg_dump_prop_clauses_file            -
% 3.65/1.01  --dbg_out_stat                          false
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  ------ Proving...
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  % SZS status Theorem for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  fof(f14,axiom,(
% 3.65/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f30,plain,(
% 3.65/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.65/1.01    inference(ennf_transformation,[],[f14])).
% 3.65/1.01  
% 3.65/1.01  fof(f31,plain,(
% 3.65/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.65/1.01    inference(flattening,[],[f30])).
% 3.65/1.01  
% 3.65/1.01  fof(f69,plain,(
% 3.65/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f31])).
% 3.65/1.01  
% 3.65/1.01  fof(f11,axiom,(
% 3.65/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f26,plain,(
% 3.65/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.65/1.01    inference(ennf_transformation,[],[f11])).
% 3.65/1.01  
% 3.65/1.01  fof(f27,plain,(
% 3.65/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.01    inference(flattening,[],[f26])).
% 3.65/1.01  
% 3.65/1.01  fof(f44,plain,(
% 3.65/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.01    inference(nnf_transformation,[],[f27])).
% 3.65/1.01  
% 3.65/1.01  fof(f63,plain,(
% 3.65/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f44])).
% 3.65/1.01  
% 3.65/1.01  fof(f18,conjecture,(
% 3.65/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f19,negated_conjecture,(
% 3.65/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.65/1.01    inference(negated_conjecture,[],[f18])).
% 3.65/1.01  
% 3.65/1.01  fof(f36,plain,(
% 3.65/1.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.65/1.01    inference(ennf_transformation,[],[f19])).
% 3.65/1.01  
% 3.65/1.01  fof(f37,plain,(
% 3.65/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.65/1.01    inference(flattening,[],[f36])).
% 3.65/1.01  
% 3.65/1.01  fof(f47,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f46,plain,(
% 3.65/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f48,plain,(
% 3.65/1.01    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f47,f46])).
% 3.65/1.01  
% 3.65/1.01  fof(f80,plain,(
% 3.65/1.01    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.65/1.01    inference(cnf_transformation,[],[f48])).
% 3.65/1.01  
% 3.65/1.01  fof(f12,axiom,(
% 3.65/1.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f65,plain,(
% 3.65/1.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f12])).
% 3.65/1.02  
% 3.65/1.02  fof(f15,axiom,(
% 3.65/1.02    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f70,plain,(
% 3.65/1.02    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f15])).
% 3.65/1.02  
% 3.65/1.02  fof(f85,plain,(
% 3.65/1.02    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.65/1.02    inference(definition_unfolding,[],[f65,f70])).
% 3.65/1.02  
% 3.65/1.02  fof(f74,plain,(
% 3.65/1.02    v1_funct_1(sK3)),
% 3.65/1.02    inference(cnf_transformation,[],[f48])).
% 3.65/1.02  
% 3.65/1.02  fof(f76,plain,(
% 3.65/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.65/1.02    inference(cnf_transformation,[],[f48])).
% 3.65/1.02  
% 3.65/1.02  fof(f77,plain,(
% 3.65/1.02    v1_funct_1(sK4)),
% 3.65/1.02    inference(cnf_transformation,[],[f48])).
% 3.65/1.02  
% 3.65/1.02  fof(f79,plain,(
% 3.65/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.65/1.02    inference(cnf_transformation,[],[f48])).
% 3.65/1.02  
% 3.65/1.02  fof(f17,axiom,(
% 3.65/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f34,plain,(
% 3.65/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.65/1.02    inference(ennf_transformation,[],[f17])).
% 3.65/1.02  
% 3.65/1.02  fof(f35,plain,(
% 3.65/1.02    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.65/1.02    inference(flattening,[],[f34])).
% 3.65/1.02  
% 3.65/1.02  fof(f72,plain,(
% 3.65/1.02    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f35])).
% 3.65/1.02  
% 3.65/1.02  fof(f75,plain,(
% 3.65/1.02    v1_funct_2(sK3,sK1,sK2)),
% 3.65/1.02    inference(cnf_transformation,[],[f48])).
% 3.65/1.02  
% 3.65/1.02  fof(f78,plain,(
% 3.65/1.02    v1_funct_2(sK4,sK2,sK1)),
% 3.65/1.02    inference(cnf_transformation,[],[f48])).
% 3.65/1.02  
% 3.65/1.02  fof(f10,axiom,(
% 3.65/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f25,plain,(
% 3.65/1.02    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.02    inference(ennf_transformation,[],[f10])).
% 3.65/1.02  
% 3.65/1.02  fof(f62,plain,(
% 3.65/1.02    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.02    inference(cnf_transformation,[],[f25])).
% 3.65/1.02  
% 3.65/1.02  fof(f16,axiom,(
% 3.65/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f32,plain,(
% 3.65/1.02    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.65/1.02    inference(ennf_transformation,[],[f16])).
% 3.65/1.02  
% 3.65/1.02  fof(f33,plain,(
% 3.65/1.02    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.65/1.02    inference(flattening,[],[f32])).
% 3.65/1.02  
% 3.65/1.02  fof(f71,plain,(
% 3.65/1.02    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f33])).
% 3.65/1.02  
% 3.65/1.02  fof(f9,axiom,(
% 3.65/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f20,plain,(
% 3.65/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.65/1.02    inference(pure_predicate_removal,[],[f9])).
% 3.65/1.02  
% 3.65/1.02  fof(f24,plain,(
% 3.65/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.02    inference(ennf_transformation,[],[f20])).
% 3.65/1.02  
% 3.65/1.02  fof(f61,plain,(
% 3.65/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.02    inference(cnf_transformation,[],[f24])).
% 3.65/1.02  
% 3.65/1.02  fof(f13,axiom,(
% 3.65/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f28,plain,(
% 3.65/1.02    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.65/1.02    inference(ennf_transformation,[],[f13])).
% 3.65/1.02  
% 3.65/1.02  fof(f29,plain,(
% 3.65/1.02    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.65/1.02    inference(flattening,[],[f28])).
% 3.65/1.02  
% 3.65/1.02  fof(f45,plain,(
% 3.65/1.02    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.65/1.02    inference(nnf_transformation,[],[f29])).
% 3.65/1.02  
% 3.65/1.02  fof(f67,plain,(
% 3.65/1.02    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f45])).
% 3.65/1.02  
% 3.65/1.02  fof(f89,plain,(
% 3.65/1.02    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.65/1.02    inference(equality_resolution,[],[f67])).
% 3.65/1.02  
% 3.65/1.02  fof(f8,axiom,(
% 3.65/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f23,plain,(
% 3.65/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.02    inference(ennf_transformation,[],[f8])).
% 3.65/1.02  
% 3.65/1.02  fof(f60,plain,(
% 3.65/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.02    inference(cnf_transformation,[],[f23])).
% 3.65/1.02  
% 3.65/1.02  fof(f81,plain,(
% 3.65/1.02    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 3.65/1.02    inference(cnf_transformation,[],[f48])).
% 3.65/1.02  
% 3.65/1.02  fof(f7,axiom,(
% 3.65/1.02    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f59,plain,(
% 3.65/1.02    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.65/1.02    inference(cnf_transformation,[],[f7])).
% 3.65/1.02  
% 3.65/1.02  fof(f83,plain,(
% 3.65/1.02    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.65/1.02    inference(definition_unfolding,[],[f59,f70])).
% 3.65/1.02  
% 3.65/1.02  fof(f4,axiom,(
% 3.65/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f42,plain,(
% 3.65/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.65/1.02    inference(nnf_transformation,[],[f4])).
% 3.65/1.02  
% 3.65/1.02  fof(f43,plain,(
% 3.65/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.65/1.02    inference(flattening,[],[f42])).
% 3.65/1.02  
% 3.65/1.02  fof(f54,plain,(
% 3.65/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.65/1.02    inference(cnf_transformation,[],[f43])).
% 3.65/1.02  
% 3.65/1.02  fof(f87,plain,(
% 3.65/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.65/1.02    inference(equality_resolution,[],[f54])).
% 3.65/1.02  
% 3.65/1.02  fof(f3,axiom,(
% 3.65/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f21,plain,(
% 3.65/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.65/1.02    inference(ennf_transformation,[],[f3])).
% 3.65/1.02  
% 3.65/1.02  fof(f52,plain,(
% 3.65/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f21])).
% 3.65/1.02  
% 3.65/1.02  fof(f1,axiom,(
% 3.65/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f38,plain,(
% 3.65/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.65/1.02    inference(nnf_transformation,[],[f1])).
% 3.65/1.02  
% 3.65/1.02  fof(f39,plain,(
% 3.65/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.65/1.02    inference(rectify,[],[f38])).
% 3.65/1.02  
% 3.65/1.02  fof(f40,plain,(
% 3.65/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.65/1.02    introduced(choice_axiom,[])).
% 3.65/1.02  
% 3.65/1.02  fof(f41,plain,(
% 3.65/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.65/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.65/1.02  
% 3.65/1.02  fof(f50,plain,(
% 3.65/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f41])).
% 3.65/1.02  
% 3.65/1.02  fof(f5,axiom,(
% 3.65/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f22,plain,(
% 3.65/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.65/1.02    inference(ennf_transformation,[],[f5])).
% 3.65/1.02  
% 3.65/1.02  fof(f56,plain,(
% 3.65/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f22])).
% 3.65/1.02  
% 3.65/1.02  fof(f2,axiom,(
% 3.65/1.02    v1_xboole_0(k1_xboole_0)),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f51,plain,(
% 3.65/1.02    v1_xboole_0(k1_xboole_0)),
% 3.65/1.02    inference(cnf_transformation,[],[f2])).
% 3.65/1.02  
% 3.65/1.02  fof(f53,plain,(
% 3.65/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.65/1.02    inference(cnf_transformation,[],[f43])).
% 3.65/1.02  
% 3.65/1.02  fof(f6,axiom,(
% 3.65/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.02  
% 3.65/1.02  fof(f57,plain,(
% 3.65/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.65/1.02    inference(cnf_transformation,[],[f6])).
% 3.65/1.02  
% 3.65/1.02  fof(f82,plain,(
% 3.65/1.02    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.65/1.02    inference(definition_unfolding,[],[f57,f70])).
% 3.65/1.02  
% 3.65/1.02  cnf(c_19,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.65/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.65/1.02      | ~ v1_funct_1(X0)
% 3.65/1.02      | ~ v1_funct_1(X3) ),
% 3.65/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1056,plain,
% 3.65/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.65/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.65/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.65/1.02      | v1_funct_1(X0) != iProver_top
% 3.65/1.02      | v1_funct_1(X3) != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_15,plain,
% 3.65/1.02      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.65/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/1.02      | X3 = X2 ),
% 3.65/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_25,negated_conjecture,
% 3.65/1.02      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.65/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_438,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.02      | X3 = X0
% 3.65/1.02      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 3.65/1.02      | k6_partfun1(sK1) != X3
% 3.65/1.02      | sK1 != X2
% 3.65/1.02      | sK1 != X1 ),
% 3.65/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_439,plain,
% 3.65/1.02      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.65/1.02      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.65/1.02      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.65/1.02      inference(unflattening,[status(thm)],[c_438]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_16,plain,
% 3.65/1.02      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.65/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_447,plain,
% 3.65/1.02      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.65/1.02      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.65/1.02      inference(forward_subsumption_resolution,
% 3.65/1.02                [status(thm)],
% 3.65/1.02                [c_439,c_16]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1042,plain,
% 3.65/1.02      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.65/1.02      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2716,plain,
% 3.65/1.02      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 3.65/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.65/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.65/1.02      | v1_funct_1(sK3) != iProver_top
% 3.65/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.65/1.02      inference(superposition,[status(thm)],[c_1056,c_1042]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_31,negated_conjecture,
% 3.65/1.02      ( v1_funct_1(sK3) ),
% 3.65/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_32,plain,
% 3.65/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_29,negated_conjecture,
% 3.65/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.65/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_34,plain,
% 3.65/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_28,negated_conjecture,
% 3.65/1.02      ( v1_funct_1(sK4) ),
% 3.65/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_35,plain,
% 3.65/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_26,negated_conjecture,
% 3.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.65/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_37,plain,
% 3.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2980,plain,
% 3.65/1.02      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 3.65/1.02      inference(global_propositional_subsumption,
% 3.65/1.02                [status(thm)],
% 3.65/1.02                [c_2716,c_32,c_34,c_35,c_37]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_23,plain,
% 3.65/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.65/1.02      | ~ v1_funct_2(X3,X4,X1)
% 3.65/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.02      | ~ v1_funct_1(X0)
% 3.65/1.02      | ~ v1_funct_1(X3)
% 3.65/1.02      | v2_funct_1(X3)
% 3.65/1.02      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.65/1.02      | k1_xboole_0 = X2 ),
% 3.65/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1053,plain,
% 3.65/1.02      ( k1_xboole_0 = X0
% 3.65/1.02      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.65/1.02      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.65/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.65/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.65/1.02      | v1_funct_1(X1) != iProver_top
% 3.65/1.02      | v1_funct_1(X3) != iProver_top
% 3.65/1.02      | v2_funct_1(X3) = iProver_top
% 3.65/1.02      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_3667,plain,
% 3.65/1.02      ( sK1 = k1_xboole_0
% 3.65/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.65/1.02      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.65/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.65/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.65/1.02      | v1_funct_1(sK3) != iProver_top
% 3.65/1.02      | v1_funct_1(sK4) != iProver_top
% 3.65/1.02      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.65/1.02      | v2_funct_1(sK3) = iProver_top ),
% 3.65/1.02      inference(superposition,[status(thm)],[c_2980,c_1053]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_30,negated_conjecture,
% 3.65/1.02      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.65/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_33,plain,
% 3.65/1.02      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_27,negated_conjecture,
% 3.65/1.02      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.65/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_36,plain,
% 3.65/1.02      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1052,plain,
% 3.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_13,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.65/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1058,plain,
% 3.65/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.65/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2183,plain,
% 3.65/1.02      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.65/1.02      inference(superposition,[status(thm)],[c_1052,c_1058]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_21,plain,
% 3.65/1.02      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.65/1.02      | ~ v1_funct_2(X2,X0,X1)
% 3.65/1.02      | ~ v1_funct_2(X3,X1,X0)
% 3.65/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.65/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/1.02      | ~ v1_funct_1(X2)
% 3.65/1.02      | ~ v1_funct_1(X3)
% 3.65/1.02      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.65/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_451,plain,
% 3.65/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.65/1.02      | ~ v1_funct_2(X3,X2,X1)
% 3.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.65/1.02      | ~ v1_funct_1(X3)
% 3.65/1.02      | ~ v1_funct_1(X0)
% 3.65/1.02      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.65/1.02      | k2_relset_1(X2,X1,X3) = X1
% 3.65/1.02      | k6_partfun1(X1) != k6_partfun1(sK1)
% 3.65/1.02      | sK1 != X1 ),
% 3.65/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_452,plain,
% 3.65/1.02      ( ~ v1_funct_2(X0,X1,sK1)
% 3.65/1.02      | ~ v1_funct_2(X2,sK1,X1)
% 3.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.65/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.65/1.02      | ~ v1_funct_1(X2)
% 3.65/1.02      | ~ v1_funct_1(X0)
% 3.65/1.02      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.65/1.02      | k2_relset_1(X1,sK1,X0) = sK1
% 3.65/1.02      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 3.65/1.02      inference(unflattening,[status(thm)],[c_451]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_526,plain,
% 3.65/1.02      ( ~ v1_funct_2(X0,X1,sK1)
% 3.65/1.02      | ~ v1_funct_2(X2,sK1,X1)
% 3.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.65/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.65/1.02      | ~ v1_funct_1(X0)
% 3.65/1.02      | ~ v1_funct_1(X2)
% 3.65/1.02      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.65/1.02      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 3.65/1.02      inference(equality_resolution_simp,[status(thm)],[c_452]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1041,plain,
% 3.65/1.02      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.65/1.02      | k2_relset_1(X0,sK1,X2) = sK1
% 3.65/1.02      | v1_funct_2(X2,X0,sK1) != iProver_top
% 3.65/1.02      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.65/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.65/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.65/1.02      | v1_funct_1(X2) != iProver_top
% 3.65/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1843,plain,
% 3.65/1.02      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 3.65/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.65/1.02      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.65/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.65/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.65/1.02      | v1_funct_1(sK3) != iProver_top
% 3.65/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.65/1.02      inference(equality_resolution,[status(thm)],[c_1041]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1890,plain,
% 3.65/1.02      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.65/1.02      inference(global_propositional_subsumption,
% 3.65/1.02                [status(thm)],
% 3.65/1.02                [c_1843,c_32,c_33,c_34,c_35,c_36,c_37]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2198,plain,
% 3.65/1.02      ( k2_relat_1(sK4) = sK1 ),
% 3.65/1.02      inference(light_normalisation,[status(thm)],[c_2183,c_1890]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_12,plain,
% 3.65/1.02      ( v5_relat_1(X0,X1)
% 3.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.65/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_17,plain,
% 3.65/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.65/1.02      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.65/1.02      | ~ v1_relat_1(X0) ),
% 3.65/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_356,plain,
% 3.65/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.65/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.65/1.02      | ~ v1_relat_1(X0)
% 3.65/1.02      | X0 != X1
% 3.65/1.02      | k2_relat_1(X0) != X3 ),
% 3.65/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_357,plain,
% 3.65/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.65/1.02      | ~ v1_relat_1(X0) ),
% 3.65/1.02      inference(unflattening,[status(thm)],[c_356]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_11,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.02      | v1_relat_1(X0) ),
% 3.65/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_367,plain,
% 3.65/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.65/1.02      inference(forward_subsumption_resolution,
% 3.65/1.02                [status(thm)],
% 3.65/1.02                [c_357,c_11]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_24,negated_conjecture,
% 3.65/1.02      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 3.65/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_382,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.65/1.02      | ~ v2_funct_1(sK3)
% 3.65/1.02      | k2_relat_1(X0) != sK1
% 3.65/1.02      | sK4 != X0 ),
% 3.65/1.02      inference(resolution_lifted,[status(thm)],[c_367,c_24]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_383,plain,
% 3.65/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.65/1.02      | ~ v2_funct_1(sK3)
% 3.65/1.02      | k2_relat_1(sK4) != sK1 ),
% 3.65/1.02      inference(unflattening,[status(thm)],[c_382]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_646,plain,
% 3.65/1.02      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 3.65/1.02      inference(splitting,
% 3.65/1.02                [splitting(split),new_symbols(definition,[])],
% 3.65/1.02                [c_383]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1044,plain,
% 3.65/1.02      ( k2_relat_1(sK4) != sK1
% 3.65/1.02      | v2_funct_1(sK3) != iProver_top
% 3.65/1.02      | sP0_iProver_split = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2339,plain,
% 3.65/1.02      ( sK1 != sK1
% 3.65/1.02      | v2_funct_1(sK3) != iProver_top
% 3.65/1.02      | sP0_iProver_split = iProver_top ),
% 3.65/1.02      inference(demodulation,[status(thm)],[c_2198,c_1044]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2340,plain,
% 3.65/1.02      ( v2_funct_1(sK3) != iProver_top
% 3.65/1.02      | sP0_iProver_split = iProver_top ),
% 3.65/1.02      inference(equality_resolution_simp,[status(thm)],[c_2339]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_645,plain,
% 3.65/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.65/1.02      | ~ sP0_iProver_split ),
% 3.65/1.02      inference(splitting,
% 3.65/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.65/1.02                [c_383]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1045,plain,
% 3.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
% 3.65/1.02      | sP0_iProver_split != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2338,plain,
% 3.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.65/1.02      | sP0_iProver_split != iProver_top ),
% 3.65/1.02      inference(demodulation,[status(thm)],[c_2198,c_1045]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2356,plain,
% 3.65/1.02      ( sP0_iProver_split != iProver_top ),
% 3.65/1.02      inference(superposition,[status(thm)],[c_1052,c_2338]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_9098,plain,
% 3.65/1.02      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top | sK1 = k1_xboole_0 ),
% 3.65/1.02      inference(global_propositional_subsumption,
% 3.65/1.02                [status(thm)],
% 3.65/1.02                [c_3667,c_32,c_33,c_34,c_35,c_36,c_37,c_2340,c_2356]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_9099,plain,
% 3.65/1.02      ( sK1 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 3.65/1.02      inference(renaming,[status(thm)],[c_9098]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_9,plain,
% 3.65/1.02      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.65/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1059,plain,
% 3.65/1.02      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_9104,plain,
% 3.65/1.02      ( sK1 = k1_xboole_0 ),
% 3.65/1.02      inference(forward_subsumption_resolution,
% 3.65/1.02                [status(thm)],
% 3.65/1.02                [c_9099,c_1059]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1049,plain,
% 3.65/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_9158,plain,
% 3.65/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 3.65/1.02      inference(demodulation,[status(thm)],[c_9104,c_1049]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_5,plain,
% 3.65/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.65/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_9166,plain,
% 3.65/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.65/1.02      inference(demodulation,[status(thm)],[c_9158,c_5]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_655,plain,
% 3.65/1.02      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.65/1.02      theory(equality) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2093,plain,
% 3.65/1.02      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_655]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2094,plain,
% 3.65/1.02      ( sK3 != X0
% 3.65/1.02      | v2_funct_1(X0) != iProver_top
% 3.65/1.02      | v2_funct_1(sK3) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_2093]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2096,plain,
% 3.65/1.02      ( sK3 != k1_xboole_0
% 3.65/1.02      | v2_funct_1(sK3) = iProver_top
% 3.65/1.02      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_2094]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_3,plain,
% 3.65/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.65/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1767,plain,
% 3.65/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1768,plain,
% 3.65/1.02      ( sK3 = X0
% 3.65/1.02      | v1_xboole_0(X0) != iProver_top
% 3.65/1.02      | v1_xboole_0(sK3) != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_1767]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1770,plain,
% 3.65/1.02      ( sK3 = k1_xboole_0
% 3.65/1.02      | v1_xboole_0(sK3) != iProver_top
% 3.65/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_1768]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_0,plain,
% 3.65/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.65/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_7,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.02      | ~ r2_hidden(X2,X0)
% 3.65/1.02      | ~ v1_xboole_0(X1) ),
% 3.65/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_320,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.02      | ~ v1_xboole_0(X1)
% 3.65/1.02      | v1_xboole_0(X2)
% 3.65/1.02      | X0 != X2
% 3.65/1.02      | sK0(X2) != X3 ),
% 3.65/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_321,plain,
% 3.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.02      | ~ v1_xboole_0(X1)
% 3.65/1.02      | v1_xboole_0(X0) ),
% 3.65/1.02      inference(unflattening,[status(thm)],[c_320]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1644,plain,
% 3.65/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.65/1.02      | ~ v1_xboole_0(X0)
% 3.65/1.02      | v1_xboole_0(sK3) ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_321]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1645,plain,
% 3.65/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.65/1.02      | v1_xboole_0(X0) != iProver_top
% 3.65/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1647,plain,
% 3.65/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.65/1.02      | v1_xboole_0(sK3) = iProver_top
% 3.65/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_1645]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_649,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1548,plain,
% 3.65/1.02      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_649]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1549,plain,
% 3.65/1.02      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.65/1.02      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.65/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1272,plain,
% 3.65/1.02      ( v2_funct_1(X0)
% 3.65/1.02      | ~ v2_funct_1(k6_partfun1(X1))
% 3.65/1.02      | X0 != k6_partfun1(X1) ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_655]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1273,plain,
% 3.65/1.02      ( X0 != k6_partfun1(X1)
% 3.65/1.02      | v2_funct_1(X0) = iProver_top
% 3.65/1.02      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_1275,plain,
% 3.65/1.02      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.65/1.02      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.65/1.02      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_1273]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_2,plain,
% 3.65/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.65/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_93,plain,
% 3.65/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_89,plain,
% 3.65/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_6,plain,
% 3.65/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.65/1.02      | k1_xboole_0 = X1
% 3.65/1.02      | k1_xboole_0 = X0 ),
% 3.65/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_88,plain,
% 3.65/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.65/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_8,plain,
% 3.65/1.02      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.65/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_82,plain,
% 3.65/1.02      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.65/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(c_84,plain,
% 3.65/1.02      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.65/1.02      inference(instantiation,[status(thm)],[c_82]) ).
% 3.65/1.02  
% 3.65/1.02  cnf(contradiction,plain,
% 3.65/1.02      ( $false ),
% 3.65/1.02      inference(minisat,
% 3.65/1.02                [status(thm)],
% 3.65/1.02                [c_9166,c_2356,c_2340,c_2096,c_1770,c_1647,c_1549,c_1275,
% 3.65/1.02                 c_93,c_89,c_88,c_8,c_84]) ).
% 3.65/1.02  
% 3.65/1.02  
% 3.65/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.02  
% 3.65/1.02  ------                               Statistics
% 3.65/1.02  
% 3.65/1.02  ------ General
% 3.65/1.02  
% 3.65/1.02  abstr_ref_over_cycles:                  0
% 3.65/1.02  abstr_ref_under_cycles:                 0
% 3.65/1.02  gc_basic_clause_elim:                   0
% 3.65/1.02  forced_gc_time:                         0
% 3.65/1.02  parsing_time:                           0.014
% 3.65/1.02  unif_index_cands_time:                  0.
% 3.65/1.02  unif_index_add_time:                    0.
% 3.65/1.02  orderings_time:                         0.
% 3.65/1.02  out_proof_time:                         0.01
% 3.65/1.02  total_time:                             0.47
% 3.65/1.02  num_of_symbols:                         54
% 3.65/1.02  num_of_terms:                           13434
% 3.65/1.02  
% 3.65/1.02  ------ Preprocessing
% 3.65/1.02  
% 3.65/1.02  num_of_splits:                          1
% 3.65/1.02  num_of_split_atoms:                     1
% 3.65/1.02  num_of_reused_defs:                     0
% 3.65/1.02  num_eq_ax_congr_red:                    11
% 3.65/1.02  num_of_sem_filtered_clauses:            1
% 3.65/1.02  num_of_subtypes:                        0
% 3.65/1.02  monotx_restored_types:                  0
% 3.65/1.02  sat_num_of_epr_types:                   0
% 3.65/1.02  sat_num_of_non_cyclic_types:            0
% 3.65/1.02  sat_guarded_non_collapsed_types:        0
% 3.65/1.02  num_pure_diseq_elim:                    0
% 3.65/1.02  simp_replaced_by:                       0
% 3.65/1.02  res_preprocessed:                       133
% 3.65/1.02  prep_upred:                             0
% 3.65/1.02  prep_unflattend:                        21
% 3.65/1.02  smt_new_axioms:                         0
% 3.65/1.02  pred_elim_cands:                        5
% 3.65/1.02  pred_elim:                              5
% 3.65/1.02  pred_elim_cl:                           8
% 3.65/1.02  pred_elim_cycles:                       7
% 3.65/1.02  merged_defs:                            0
% 3.65/1.02  merged_defs_ncl:                        0
% 3.65/1.02  bin_hyper_res:                          0
% 3.65/1.02  prep_cycles:                            4
% 3.65/1.02  pred_elim_time:                         0.006
% 3.65/1.02  splitting_time:                         0.
% 3.65/1.02  sem_filter_time:                        0.
% 3.65/1.02  monotx_time:                            0.
% 3.65/1.02  subtype_inf_time:                       0.
% 3.65/1.02  
% 3.65/1.02  ------ Problem properties
% 3.65/1.02  
% 3.65/1.02  clauses:                                25
% 3.65/1.02  conjectures:                            6
% 3.65/1.02  epr:                                    6
% 3.65/1.02  horn:                                   23
% 3.65/1.02  ground:                                 10
% 3.65/1.02  unary:                                  12
% 3.65/1.02  binary:                                 3
% 3.65/1.02  lits:                                   73
% 3.65/1.02  lits_eq:                                15
% 3.65/1.02  fd_pure:                                0
% 3.65/1.02  fd_pseudo:                              0
% 3.65/1.02  fd_cond:                                2
% 3.65/1.02  fd_pseudo_cond:                         1
% 3.65/1.02  ac_symbols:                             0
% 3.65/1.02  
% 3.65/1.02  ------ Propositional Solver
% 3.65/1.02  
% 3.65/1.02  prop_solver_calls:                      28
% 3.65/1.02  prop_fast_solver_calls:                 1277
% 3.65/1.02  smt_solver_calls:                       0
% 3.65/1.02  smt_fast_solver_calls:                  0
% 3.65/1.02  prop_num_of_clauses:                    3946
% 3.65/1.02  prop_preprocess_simplified:             7498
% 3.65/1.02  prop_fo_subsumed:                       39
% 3.65/1.02  prop_solver_time:                       0.
% 3.65/1.02  smt_solver_time:                        0.
% 3.65/1.02  smt_fast_solver_time:                   0.
% 3.65/1.02  prop_fast_solver_time:                  0.
% 3.65/1.02  prop_unsat_core_time:                   0.
% 3.65/1.02  
% 3.65/1.02  ------ QBF
% 3.65/1.02  
% 3.65/1.02  qbf_q_res:                              0
% 3.65/1.02  qbf_num_tautologies:                    0
% 3.65/1.02  qbf_prep_cycles:                        0
% 3.65/1.02  
% 3.65/1.02  ------ BMC1
% 3.65/1.02  
% 3.65/1.02  bmc1_current_bound:                     -1
% 3.65/1.02  bmc1_last_solved_bound:                 -1
% 3.65/1.02  bmc1_unsat_core_size:                   -1
% 3.65/1.02  bmc1_unsat_core_parents_size:           -1
% 3.65/1.02  bmc1_merge_next_fun:                    0
% 3.65/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.65/1.02  
% 3.65/1.02  ------ Instantiation
% 3.65/1.02  
% 3.65/1.02  inst_num_of_clauses:                    1098
% 3.65/1.02  inst_num_in_passive:                    208
% 3.65/1.02  inst_num_in_active:                     542
% 3.65/1.02  inst_num_in_unprocessed:                348
% 3.65/1.02  inst_num_of_loops:                      560
% 3.65/1.02  inst_num_of_learning_restarts:          0
% 3.65/1.02  inst_num_moves_active_passive:          14
% 3.65/1.02  inst_lit_activity:                      0
% 3.65/1.02  inst_lit_activity_moves:                0
% 3.65/1.02  inst_num_tautologies:                   0
% 3.65/1.02  inst_num_prop_implied:                  0
% 3.65/1.02  inst_num_existing_simplified:           0
% 3.65/1.02  inst_num_eq_res_simplified:             0
% 3.65/1.02  inst_num_child_elim:                    0
% 3.65/1.02  inst_num_of_dismatching_blockings:      163
% 3.65/1.02  inst_num_of_non_proper_insts:           1013
% 3.65/1.02  inst_num_of_duplicates:                 0
% 3.65/1.02  inst_inst_num_from_inst_to_res:         0
% 3.65/1.02  inst_dismatching_checking_time:         0.
% 3.65/1.02  
% 3.65/1.02  ------ Resolution
% 3.65/1.02  
% 3.65/1.02  res_num_of_clauses:                     0
% 3.65/1.02  res_num_in_passive:                     0
% 3.65/1.02  res_num_in_active:                      0
% 3.65/1.02  res_num_of_loops:                       137
% 3.65/1.02  res_forward_subset_subsumed:            28
% 3.65/1.02  res_backward_subset_subsumed:           0
% 3.65/1.02  res_forward_subsumed:                   0
% 3.65/1.02  res_backward_subsumed:                  0
% 3.65/1.02  res_forward_subsumption_resolution:     4
% 3.65/1.02  res_backward_subsumption_resolution:    0
% 3.65/1.02  res_clause_to_clause_subsumption:       2246
% 3.65/1.02  res_orphan_elimination:                 0
% 3.65/1.02  res_tautology_del:                      52
% 3.65/1.02  res_num_eq_res_simplified:              1
% 3.65/1.02  res_num_sel_changes:                    0
% 3.65/1.02  res_moves_from_active_to_pass:          0
% 3.65/1.02  
% 3.65/1.02  ------ Superposition
% 3.65/1.02  
% 3.65/1.02  sup_time_total:                         0.
% 3.65/1.02  sup_time_generating:                    0.
% 3.65/1.02  sup_time_sim_full:                      0.
% 3.65/1.02  sup_time_sim_immed:                     0.
% 3.65/1.02  
% 3.65/1.02  sup_num_of_clauses:                     170
% 3.65/1.02  sup_num_in_active:                      46
% 3.65/1.02  sup_num_in_passive:                     124
% 3.65/1.02  sup_num_of_loops:                       110
% 3.65/1.02  sup_fw_superposition:                   166
% 3.65/1.02  sup_bw_superposition:                   17
% 3.65/1.02  sup_immediate_simplified:               48
% 3.65/1.02  sup_given_eliminated:                   1
% 3.65/1.02  comparisons_done:                       0
% 3.65/1.02  comparisons_avoided:                    0
% 3.65/1.02  
% 3.65/1.02  ------ Simplifications
% 3.65/1.02  
% 3.65/1.02  
% 3.65/1.02  sim_fw_subset_subsumed:                 0
% 3.65/1.02  sim_bw_subset_subsumed:                 6
% 3.65/1.02  sim_fw_subsumed:                        5
% 3.65/1.02  sim_bw_subsumed:                        5
% 3.65/1.02  sim_fw_subsumption_res:                 11
% 3.65/1.02  sim_bw_subsumption_res:                 0
% 3.65/1.02  sim_tautology_del:                      2
% 3.65/1.02  sim_eq_tautology_del:                   4
% 3.65/1.02  sim_eq_res_simp:                        1
% 3.65/1.02  sim_fw_demodulated:                     22
% 3.65/1.02  sim_bw_demodulated:                     60
% 3.65/1.02  sim_light_normalised:                   10
% 3.65/1.02  sim_joinable_taut:                      0
% 3.65/1.02  sim_joinable_simp:                      0
% 3.65/1.02  sim_ac_normalised:                      0
% 3.65/1.02  sim_smt_subsumption:                    0
% 3.65/1.02  
%------------------------------------------------------------------------------
