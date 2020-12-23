%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:06 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 770 expanded)
%              Number of clauses        :   92 ( 236 expanded)
%              Number of leaves         :   21 ( 191 expanded)
%              Depth                    :   21
%              Number of atoms          :  546 (4890 expanded)
%              Number of equality atoms :  214 ( 452 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f42,f41])).

fof(f72,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f64,plain,(
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

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f63,plain,(
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

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f49,f62])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_969,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_405,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_13,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_413,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_405,c_13])).

cnf(c_955,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_2605,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_955])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2766,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2605,c_29,c_31,c_32,c_34])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_966,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2793,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_966])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_965,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_971,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1993,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_965,c_971])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_418,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_490,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_418])).

cnf(c_954,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_1658,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_954])).

cnf(c_1790,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1658,c_29,c_30,c_31,c_32,c_33,c_34])).

cnf(c_2008,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1993,c_1790])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_322,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_323,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_333,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_323,c_8])).

cnf(c_21,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_333,c_21])).

cnf(c_349,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_600,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_349])).

cnf(c_957,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_2141,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2008,c_957])).

cnf(c_2142,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2141])).

cnf(c_599,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_349])).

cnf(c_958,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_2140,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2008,c_958])).

cnf(c_2158,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_965,c_2140])).

cnf(c_2973,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_29,c_30,c_31,c_32,c_33,c_34,c_2142,c_2158])).

cnf(c_2974,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2973])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_972,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2979,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2974,c_972])).

cnf(c_962,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2987,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2979,c_962])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2995,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2987,c_2])).

cnf(c_603,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1594,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_2298,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_2299,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2298])).

cnf(c_608,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1913,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_1914,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_1916,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_1475,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1476,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_602,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1326,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_1280,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_1283,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_1168,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_1169,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1168])).

cnf(c_1171,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_85,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_81,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2995,c_2299,c_2158,c_2142,c_1916,c_1476,c_1326,c_1283,c_1171,c_86,c_85,c_5,c_81])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.94/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/1.00  
% 2.94/1.00  ------  iProver source info
% 2.94/1.00  
% 2.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/1.00  git: non_committed_changes: false
% 2.94/1.00  git: last_make_outside_of_git: false
% 2.94/1.00  
% 2.94/1.00  ------ 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options
% 2.94/1.00  
% 2.94/1.00  --out_options                           all
% 2.94/1.00  --tptp_safe_out                         true
% 2.94/1.00  --problem_path                          ""
% 2.94/1.00  --include_path                          ""
% 2.94/1.00  --clausifier                            res/vclausify_rel
% 2.94/1.00  --clausifier_options                    --mode clausify
% 2.94/1.00  --stdin                                 false
% 2.94/1.00  --stats_out                             all
% 2.94/1.00  
% 2.94/1.00  ------ General Options
% 2.94/1.00  
% 2.94/1.00  --fof                                   false
% 2.94/1.00  --time_out_real                         305.
% 2.94/1.00  --time_out_virtual                      -1.
% 2.94/1.00  --symbol_type_check                     false
% 2.94/1.00  --clausify_out                          false
% 2.94/1.00  --sig_cnt_out                           false
% 2.94/1.00  --trig_cnt_out                          false
% 2.94/1.00  --trig_cnt_out_tolerance                1.
% 2.94/1.00  --trig_cnt_out_sk_spl                   false
% 2.94/1.00  --abstr_cl_out                          false
% 2.94/1.00  
% 2.94/1.00  ------ Global Options
% 2.94/1.00  
% 2.94/1.00  --schedule                              default
% 2.94/1.00  --add_important_lit                     false
% 2.94/1.00  --prop_solver_per_cl                    1000
% 2.94/1.00  --min_unsat_core                        false
% 2.94/1.00  --soft_assumptions                      false
% 2.94/1.00  --soft_lemma_size                       3
% 2.94/1.00  --prop_impl_unit_size                   0
% 2.94/1.00  --prop_impl_unit                        []
% 2.94/1.00  --share_sel_clauses                     true
% 2.94/1.00  --reset_solvers                         false
% 2.94/1.00  --bc_imp_inh                            [conj_cone]
% 2.94/1.00  --conj_cone_tolerance                   3.
% 2.94/1.00  --extra_neg_conj                        none
% 2.94/1.00  --large_theory_mode                     true
% 2.94/1.00  --prolific_symb_bound                   200
% 2.94/1.00  --lt_threshold                          2000
% 2.94/1.00  --clause_weak_htbl                      true
% 2.94/1.00  --gc_record_bc_elim                     false
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing Options
% 2.94/1.00  
% 2.94/1.00  --preprocessing_flag                    true
% 2.94/1.00  --time_out_prep_mult                    0.1
% 2.94/1.00  --splitting_mode                        input
% 2.94/1.00  --splitting_grd                         true
% 2.94/1.00  --splitting_cvd                         false
% 2.94/1.00  --splitting_cvd_svl                     false
% 2.94/1.00  --splitting_nvd                         32
% 2.94/1.00  --sub_typing                            true
% 2.94/1.00  --prep_gs_sim                           true
% 2.94/1.00  --prep_unflatten                        true
% 2.94/1.00  --prep_res_sim                          true
% 2.94/1.00  --prep_upred                            true
% 2.94/1.00  --prep_sem_filter                       exhaustive
% 2.94/1.00  --prep_sem_filter_out                   false
% 2.94/1.00  --pred_elim                             true
% 2.94/1.00  --res_sim_input                         true
% 2.94/1.00  --eq_ax_congr_red                       true
% 2.94/1.00  --pure_diseq_elim                       true
% 2.94/1.00  --brand_transform                       false
% 2.94/1.00  --non_eq_to_eq                          false
% 2.94/1.00  --prep_def_merge                        true
% 2.94/1.00  --prep_def_merge_prop_impl              false
% 2.94/1.00  --prep_def_merge_mbd                    true
% 2.94/1.00  --prep_def_merge_tr_red                 false
% 2.94/1.00  --prep_def_merge_tr_cl                  false
% 2.94/1.00  --smt_preprocessing                     true
% 2.94/1.00  --smt_ac_axioms                         fast
% 2.94/1.00  --preprocessed_out                      false
% 2.94/1.00  --preprocessed_stats                    false
% 2.94/1.00  
% 2.94/1.00  ------ Abstraction refinement Options
% 2.94/1.00  
% 2.94/1.00  --abstr_ref                             []
% 2.94/1.00  --abstr_ref_prep                        false
% 2.94/1.00  --abstr_ref_until_sat                   false
% 2.94/1.00  --abstr_ref_sig_restrict                funpre
% 2.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.00  --abstr_ref_under                       []
% 2.94/1.00  
% 2.94/1.00  ------ SAT Options
% 2.94/1.00  
% 2.94/1.00  --sat_mode                              false
% 2.94/1.00  --sat_fm_restart_options                ""
% 2.94/1.00  --sat_gr_def                            false
% 2.94/1.00  --sat_epr_types                         true
% 2.94/1.00  --sat_non_cyclic_types                  false
% 2.94/1.00  --sat_finite_models                     false
% 2.94/1.00  --sat_fm_lemmas                         false
% 2.94/1.00  --sat_fm_prep                           false
% 2.94/1.00  --sat_fm_uc_incr                        true
% 2.94/1.00  --sat_out_model                         small
% 2.94/1.00  --sat_out_clauses                       false
% 2.94/1.00  
% 2.94/1.00  ------ QBF Options
% 2.94/1.00  
% 2.94/1.00  --qbf_mode                              false
% 2.94/1.00  --qbf_elim_univ                         false
% 2.94/1.00  --qbf_dom_inst                          none
% 2.94/1.00  --qbf_dom_pre_inst                      false
% 2.94/1.00  --qbf_sk_in                             false
% 2.94/1.00  --qbf_pred_elim                         true
% 2.94/1.00  --qbf_split                             512
% 2.94/1.00  
% 2.94/1.00  ------ BMC1 Options
% 2.94/1.00  
% 2.94/1.00  --bmc1_incremental                      false
% 2.94/1.00  --bmc1_axioms                           reachable_all
% 2.94/1.00  --bmc1_min_bound                        0
% 2.94/1.00  --bmc1_max_bound                        -1
% 2.94/1.00  --bmc1_max_bound_default                -1
% 2.94/1.00  --bmc1_symbol_reachability              true
% 2.94/1.00  --bmc1_property_lemmas                  false
% 2.94/1.00  --bmc1_k_induction                      false
% 2.94/1.00  --bmc1_non_equiv_states                 false
% 2.94/1.00  --bmc1_deadlock                         false
% 2.94/1.00  --bmc1_ucm                              false
% 2.94/1.00  --bmc1_add_unsat_core                   none
% 2.94/1.00  --bmc1_unsat_core_children              false
% 2.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.00  --bmc1_out_stat                         full
% 2.94/1.00  --bmc1_ground_init                      false
% 2.94/1.00  --bmc1_pre_inst_next_state              false
% 2.94/1.00  --bmc1_pre_inst_state                   false
% 2.94/1.00  --bmc1_pre_inst_reach_state             false
% 2.94/1.00  --bmc1_out_unsat_core                   false
% 2.94/1.00  --bmc1_aig_witness_out                  false
% 2.94/1.00  --bmc1_verbose                          false
% 2.94/1.00  --bmc1_dump_clauses_tptp                false
% 2.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.00  --bmc1_dump_file                        -
% 2.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.00  --bmc1_ucm_extend_mode                  1
% 2.94/1.00  --bmc1_ucm_init_mode                    2
% 2.94/1.00  --bmc1_ucm_cone_mode                    none
% 2.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.00  --bmc1_ucm_relax_model                  4
% 2.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.00  --bmc1_ucm_layered_model                none
% 2.94/1.00  --bmc1_ucm_max_lemma_size               10
% 2.94/1.00  
% 2.94/1.00  ------ AIG Options
% 2.94/1.00  
% 2.94/1.00  --aig_mode                              false
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation Options
% 2.94/1.00  
% 2.94/1.00  --instantiation_flag                    true
% 2.94/1.00  --inst_sos_flag                         false
% 2.94/1.00  --inst_sos_phase                        true
% 2.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel_side                     num_symb
% 2.94/1.00  --inst_solver_per_active                1400
% 2.94/1.00  --inst_solver_calls_frac                1.
% 2.94/1.00  --inst_passive_queue_type               priority_queues
% 2.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.00  --inst_passive_queues_freq              [25;2]
% 2.94/1.00  --inst_dismatching                      true
% 2.94/1.00  --inst_eager_unprocessed_to_passive     true
% 2.94/1.00  --inst_prop_sim_given                   true
% 2.94/1.00  --inst_prop_sim_new                     false
% 2.94/1.00  --inst_subs_new                         false
% 2.94/1.00  --inst_eq_res_simp                      false
% 2.94/1.00  --inst_subs_given                       false
% 2.94/1.00  --inst_orphan_elimination               true
% 2.94/1.00  --inst_learning_loop_flag               true
% 2.94/1.00  --inst_learning_start                   3000
% 2.94/1.00  --inst_learning_factor                  2
% 2.94/1.00  --inst_start_prop_sim_after_learn       3
% 2.94/1.00  --inst_sel_renew                        solver
% 2.94/1.00  --inst_lit_activity_flag                true
% 2.94/1.00  --inst_restr_to_given                   false
% 2.94/1.00  --inst_activity_threshold               500
% 2.94/1.00  --inst_out_proof                        true
% 2.94/1.00  
% 2.94/1.00  ------ Resolution Options
% 2.94/1.00  
% 2.94/1.00  --resolution_flag                       true
% 2.94/1.00  --res_lit_sel                           adaptive
% 2.94/1.00  --res_lit_sel_side                      none
% 2.94/1.00  --res_ordering                          kbo
% 2.94/1.00  --res_to_prop_solver                    active
% 2.94/1.00  --res_prop_simpl_new                    false
% 2.94/1.00  --res_prop_simpl_given                  true
% 2.94/1.00  --res_passive_queue_type                priority_queues
% 2.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.00  --res_passive_queues_freq               [15;5]
% 2.94/1.00  --res_forward_subs                      full
% 2.94/1.00  --res_backward_subs                     full
% 2.94/1.00  --res_forward_subs_resolution           true
% 2.94/1.00  --res_backward_subs_resolution          true
% 2.94/1.00  --res_orphan_elimination                true
% 2.94/1.00  --res_time_limit                        2.
% 2.94/1.00  --res_out_proof                         true
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Options
% 2.94/1.00  
% 2.94/1.00  --superposition_flag                    true
% 2.94/1.00  --sup_passive_queue_type                priority_queues
% 2.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.00  --demod_completeness_check              fast
% 2.94/1.00  --demod_use_ground                      true
% 2.94/1.00  --sup_to_prop_solver                    passive
% 2.94/1.00  --sup_prop_simpl_new                    true
% 2.94/1.00  --sup_prop_simpl_given                  true
% 2.94/1.00  --sup_fun_splitting                     false
% 2.94/1.00  --sup_smt_interval                      50000
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Simplification Setup
% 2.94/1.00  
% 2.94/1.00  --sup_indices_passive                   []
% 2.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_full_bw                           [BwDemod]
% 2.94/1.00  --sup_immed_triv                        [TrivRules]
% 2.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_immed_bw_main                     []
% 2.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  
% 2.94/1.00  ------ Combination Options
% 2.94/1.00  
% 2.94/1.00  --comb_res_mult                         3
% 2.94/1.00  --comb_sup_mult                         2
% 2.94/1.00  --comb_inst_mult                        10
% 2.94/1.00  
% 2.94/1.00  ------ Debug Options
% 2.94/1.00  
% 2.94/1.00  --dbg_backtrace                         false
% 2.94/1.00  --dbg_dump_prop_clauses                 false
% 2.94/1.00  --dbg_dump_prop_clauses_file            -
% 2.94/1.00  --dbg_out_stat                          false
% 2.94/1.00  ------ Parsing...
% 2.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/1.00  ------ Proving...
% 2.94/1.00  ------ Problem Properties 
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  clauses                                 23
% 2.94/1.00  conjectures                             6
% 2.94/1.00  EPR                                     4
% 2.94/1.00  Horn                                    21
% 2.94/1.00  unary                                   11
% 2.94/1.00  binary                                  4
% 2.94/1.00  lits                                    68
% 2.94/1.00  lits eq                                 15
% 2.94/1.00  fd_pure                                 0
% 2.94/1.00  fd_pseudo                               0
% 2.94/1.00  fd_cond                                 3
% 2.94/1.00  fd_pseudo_cond                          0
% 2.94/1.00  AC symbols                              0
% 2.94/1.00  
% 2.94/1.00  ------ Schedule dynamic 5 is on 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  ------ 
% 2.94/1.00  Current options:
% 2.94/1.00  ------ 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options
% 2.94/1.00  
% 2.94/1.00  --out_options                           all
% 2.94/1.00  --tptp_safe_out                         true
% 2.94/1.00  --problem_path                          ""
% 2.94/1.00  --include_path                          ""
% 2.94/1.00  --clausifier                            res/vclausify_rel
% 2.94/1.00  --clausifier_options                    --mode clausify
% 2.94/1.00  --stdin                                 false
% 2.94/1.00  --stats_out                             all
% 2.94/1.00  
% 2.94/1.00  ------ General Options
% 2.94/1.00  
% 2.94/1.00  --fof                                   false
% 2.94/1.00  --time_out_real                         305.
% 2.94/1.00  --time_out_virtual                      -1.
% 2.94/1.00  --symbol_type_check                     false
% 2.94/1.00  --clausify_out                          false
% 2.94/1.00  --sig_cnt_out                           false
% 2.94/1.00  --trig_cnt_out                          false
% 2.94/1.00  --trig_cnt_out_tolerance                1.
% 2.94/1.00  --trig_cnt_out_sk_spl                   false
% 2.94/1.00  --abstr_cl_out                          false
% 2.94/1.00  
% 2.94/1.00  ------ Global Options
% 2.94/1.00  
% 2.94/1.00  --schedule                              default
% 2.94/1.00  --add_important_lit                     false
% 2.94/1.00  --prop_solver_per_cl                    1000
% 2.94/1.00  --min_unsat_core                        false
% 2.94/1.00  --soft_assumptions                      false
% 2.94/1.00  --soft_lemma_size                       3
% 2.94/1.00  --prop_impl_unit_size                   0
% 2.94/1.00  --prop_impl_unit                        []
% 2.94/1.00  --share_sel_clauses                     true
% 2.94/1.00  --reset_solvers                         false
% 2.94/1.00  --bc_imp_inh                            [conj_cone]
% 2.94/1.00  --conj_cone_tolerance                   3.
% 2.94/1.00  --extra_neg_conj                        none
% 2.94/1.00  --large_theory_mode                     true
% 2.94/1.00  --prolific_symb_bound                   200
% 2.94/1.00  --lt_threshold                          2000
% 2.94/1.00  --clause_weak_htbl                      true
% 2.94/1.00  --gc_record_bc_elim                     false
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing Options
% 2.94/1.00  
% 2.94/1.00  --preprocessing_flag                    true
% 2.94/1.00  --time_out_prep_mult                    0.1
% 2.94/1.00  --splitting_mode                        input
% 2.94/1.00  --splitting_grd                         true
% 2.94/1.00  --splitting_cvd                         false
% 2.94/1.00  --splitting_cvd_svl                     false
% 2.94/1.00  --splitting_nvd                         32
% 2.94/1.00  --sub_typing                            true
% 2.94/1.00  --prep_gs_sim                           true
% 2.94/1.00  --prep_unflatten                        true
% 2.94/1.00  --prep_res_sim                          true
% 2.94/1.00  --prep_upred                            true
% 2.94/1.00  --prep_sem_filter                       exhaustive
% 2.94/1.00  --prep_sem_filter_out                   false
% 2.94/1.00  --pred_elim                             true
% 2.94/1.00  --res_sim_input                         true
% 2.94/1.00  --eq_ax_congr_red                       true
% 2.94/1.00  --pure_diseq_elim                       true
% 2.94/1.00  --brand_transform                       false
% 2.94/1.00  --non_eq_to_eq                          false
% 2.94/1.00  --prep_def_merge                        true
% 2.94/1.00  --prep_def_merge_prop_impl              false
% 2.94/1.00  --prep_def_merge_mbd                    true
% 2.94/1.00  --prep_def_merge_tr_red                 false
% 2.94/1.00  --prep_def_merge_tr_cl                  false
% 2.94/1.00  --smt_preprocessing                     true
% 2.94/1.00  --smt_ac_axioms                         fast
% 2.94/1.00  --preprocessed_out                      false
% 2.94/1.00  --preprocessed_stats                    false
% 2.94/1.00  
% 2.94/1.00  ------ Abstraction refinement Options
% 2.94/1.00  
% 2.94/1.00  --abstr_ref                             []
% 2.94/1.00  --abstr_ref_prep                        false
% 2.94/1.00  --abstr_ref_until_sat                   false
% 2.94/1.00  --abstr_ref_sig_restrict                funpre
% 2.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.00  --abstr_ref_under                       []
% 2.94/1.00  
% 2.94/1.00  ------ SAT Options
% 2.94/1.00  
% 2.94/1.00  --sat_mode                              false
% 2.94/1.00  --sat_fm_restart_options                ""
% 2.94/1.00  --sat_gr_def                            false
% 2.94/1.00  --sat_epr_types                         true
% 2.94/1.00  --sat_non_cyclic_types                  false
% 2.94/1.00  --sat_finite_models                     false
% 2.94/1.00  --sat_fm_lemmas                         false
% 2.94/1.00  --sat_fm_prep                           false
% 2.94/1.00  --sat_fm_uc_incr                        true
% 2.94/1.00  --sat_out_model                         small
% 2.94/1.00  --sat_out_clauses                       false
% 2.94/1.00  
% 2.94/1.00  ------ QBF Options
% 2.94/1.00  
% 2.94/1.00  --qbf_mode                              false
% 2.94/1.00  --qbf_elim_univ                         false
% 2.94/1.00  --qbf_dom_inst                          none
% 2.94/1.00  --qbf_dom_pre_inst                      false
% 2.94/1.00  --qbf_sk_in                             false
% 2.94/1.00  --qbf_pred_elim                         true
% 2.94/1.00  --qbf_split                             512
% 2.94/1.00  
% 2.94/1.00  ------ BMC1 Options
% 2.94/1.00  
% 2.94/1.00  --bmc1_incremental                      false
% 2.94/1.00  --bmc1_axioms                           reachable_all
% 2.94/1.00  --bmc1_min_bound                        0
% 2.94/1.00  --bmc1_max_bound                        -1
% 2.94/1.00  --bmc1_max_bound_default                -1
% 2.94/1.00  --bmc1_symbol_reachability              true
% 2.94/1.00  --bmc1_property_lemmas                  false
% 2.94/1.00  --bmc1_k_induction                      false
% 2.94/1.00  --bmc1_non_equiv_states                 false
% 2.94/1.00  --bmc1_deadlock                         false
% 2.94/1.00  --bmc1_ucm                              false
% 2.94/1.00  --bmc1_add_unsat_core                   none
% 2.94/1.00  --bmc1_unsat_core_children              false
% 2.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.00  --bmc1_out_stat                         full
% 2.94/1.00  --bmc1_ground_init                      false
% 2.94/1.00  --bmc1_pre_inst_next_state              false
% 2.94/1.00  --bmc1_pre_inst_state                   false
% 2.94/1.00  --bmc1_pre_inst_reach_state             false
% 2.94/1.00  --bmc1_out_unsat_core                   false
% 2.94/1.00  --bmc1_aig_witness_out                  false
% 2.94/1.00  --bmc1_verbose                          false
% 2.94/1.00  --bmc1_dump_clauses_tptp                false
% 2.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.00  --bmc1_dump_file                        -
% 2.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.00  --bmc1_ucm_extend_mode                  1
% 2.94/1.00  --bmc1_ucm_init_mode                    2
% 2.94/1.00  --bmc1_ucm_cone_mode                    none
% 2.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.00  --bmc1_ucm_relax_model                  4
% 2.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.00  --bmc1_ucm_layered_model                none
% 2.94/1.00  --bmc1_ucm_max_lemma_size               10
% 2.94/1.00  
% 2.94/1.00  ------ AIG Options
% 2.94/1.00  
% 2.94/1.00  --aig_mode                              false
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation Options
% 2.94/1.00  
% 2.94/1.00  --instantiation_flag                    true
% 2.94/1.00  --inst_sos_flag                         false
% 2.94/1.00  --inst_sos_phase                        true
% 2.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel_side                     none
% 2.94/1.00  --inst_solver_per_active                1400
% 2.94/1.00  --inst_solver_calls_frac                1.
% 2.94/1.00  --inst_passive_queue_type               priority_queues
% 2.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.00  --inst_passive_queues_freq              [25;2]
% 2.94/1.00  --inst_dismatching                      true
% 2.94/1.00  --inst_eager_unprocessed_to_passive     true
% 2.94/1.00  --inst_prop_sim_given                   true
% 2.94/1.00  --inst_prop_sim_new                     false
% 2.94/1.00  --inst_subs_new                         false
% 2.94/1.00  --inst_eq_res_simp                      false
% 2.94/1.00  --inst_subs_given                       false
% 2.94/1.00  --inst_orphan_elimination               true
% 2.94/1.00  --inst_learning_loop_flag               true
% 2.94/1.00  --inst_learning_start                   3000
% 2.94/1.00  --inst_learning_factor                  2
% 2.94/1.00  --inst_start_prop_sim_after_learn       3
% 2.94/1.00  --inst_sel_renew                        solver
% 2.94/1.00  --inst_lit_activity_flag                true
% 2.94/1.00  --inst_restr_to_given                   false
% 2.94/1.00  --inst_activity_threshold               500
% 2.94/1.00  --inst_out_proof                        true
% 2.94/1.00  
% 2.94/1.00  ------ Resolution Options
% 2.94/1.00  
% 2.94/1.00  --resolution_flag                       false
% 2.94/1.00  --res_lit_sel                           adaptive
% 2.94/1.00  --res_lit_sel_side                      none
% 2.94/1.00  --res_ordering                          kbo
% 2.94/1.00  --res_to_prop_solver                    active
% 2.94/1.00  --res_prop_simpl_new                    false
% 2.94/1.00  --res_prop_simpl_given                  true
% 2.94/1.00  --res_passive_queue_type                priority_queues
% 2.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.00  --res_passive_queues_freq               [15;5]
% 2.94/1.00  --res_forward_subs                      full
% 2.94/1.00  --res_backward_subs                     full
% 2.94/1.00  --res_forward_subs_resolution           true
% 2.94/1.00  --res_backward_subs_resolution          true
% 2.94/1.00  --res_orphan_elimination                true
% 2.94/1.00  --res_time_limit                        2.
% 2.94/1.00  --res_out_proof                         true
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Options
% 2.94/1.00  
% 2.94/1.00  --superposition_flag                    true
% 2.94/1.00  --sup_passive_queue_type                priority_queues
% 2.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.00  --demod_completeness_check              fast
% 2.94/1.00  --demod_use_ground                      true
% 2.94/1.00  --sup_to_prop_solver                    passive
% 2.94/1.00  --sup_prop_simpl_new                    true
% 2.94/1.00  --sup_prop_simpl_given                  true
% 2.94/1.00  --sup_fun_splitting                     false
% 2.94/1.00  --sup_smt_interval                      50000
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Simplification Setup
% 2.94/1.00  
% 2.94/1.00  --sup_indices_passive                   []
% 2.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_full_bw                           [BwDemod]
% 2.94/1.00  --sup_immed_triv                        [TrivRules]
% 2.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_immed_bw_main                     []
% 2.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  
% 2.94/1.00  ------ Combination Options
% 2.94/1.00  
% 2.94/1.00  --comb_res_mult                         3
% 2.94/1.00  --comb_sup_mult                         2
% 2.94/1.00  --comb_inst_mult                        10
% 2.94/1.00  
% 2.94/1.00  ------ Debug Options
% 2.94/1.00  
% 2.94/1.00  --dbg_backtrace                         false
% 2.94/1.00  --dbg_dump_prop_clauses                 false
% 2.94/1.00  --dbg_dump_prop_clauses_file            -
% 2.94/1.00  --dbg_out_stat                          false
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  ------ Proving...
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  % SZS status Theorem for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  fof(f12,axiom,(
% 2.94/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f29,plain,(
% 2.94/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.94/1.00    inference(ennf_transformation,[],[f12])).
% 2.94/1.00  
% 2.94/1.00  fof(f30,plain,(
% 2.94/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.94/1.00    inference(flattening,[],[f29])).
% 2.94/1.00  
% 2.94/1.00  fof(f61,plain,(
% 2.94/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f30])).
% 2.94/1.00  
% 2.94/1.00  fof(f9,axiom,(
% 2.94/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f25,plain,(
% 2.94/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.94/1.00    inference(ennf_transformation,[],[f9])).
% 2.94/1.00  
% 2.94/1.00  fof(f26,plain,(
% 2.94/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(flattening,[],[f25])).
% 2.94/1.00  
% 2.94/1.00  fof(f39,plain,(
% 2.94/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(nnf_transformation,[],[f26])).
% 2.94/1.00  
% 2.94/1.00  fof(f55,plain,(
% 2.94/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f39])).
% 2.94/1.00  
% 2.94/1.00  fof(f16,conjecture,(
% 2.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f17,negated_conjecture,(
% 2.94/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.94/1.00    inference(negated_conjecture,[],[f16])).
% 2.94/1.00  
% 2.94/1.00  fof(f35,plain,(
% 2.94/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.94/1.00    inference(ennf_transformation,[],[f17])).
% 2.94/1.00  
% 2.94/1.00  fof(f36,plain,(
% 2.94/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.94/1.00    inference(flattening,[],[f35])).
% 2.94/1.00  
% 2.94/1.00  fof(f42,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f41,plain,(
% 2.94/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f43,plain,(
% 2.94/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f42,f41])).
% 2.94/1.00  
% 2.94/1.00  fof(f72,plain,(
% 2.94/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f10,axiom,(
% 2.94/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f57,plain,(
% 2.94/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f10])).
% 2.94/1.00  
% 2.94/1.00  fof(f13,axiom,(
% 2.94/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f62,plain,(
% 2.94/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f13])).
% 2.94/1.00  
% 2.94/1.00  fof(f77,plain,(
% 2.94/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.94/1.00    inference(definition_unfolding,[],[f57,f62])).
% 2.94/1.00  
% 2.94/1.00  fof(f66,plain,(
% 2.94/1.00    v1_funct_1(sK2)),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f68,plain,(
% 2.94/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f69,plain,(
% 2.94/1.00    v1_funct_1(sK3)),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f71,plain,(
% 2.94/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f15,axiom,(
% 2.94/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f33,plain,(
% 2.94/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.94/1.00    inference(ennf_transformation,[],[f15])).
% 2.94/1.00  
% 2.94/1.00  fof(f34,plain,(
% 2.94/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.94/1.00    inference(flattening,[],[f33])).
% 2.94/1.00  
% 2.94/1.00  fof(f64,plain,(
% 2.94/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f34])).
% 2.94/1.00  
% 2.94/1.00  fof(f67,plain,(
% 2.94/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f70,plain,(
% 2.94/1.00    v1_funct_2(sK3,sK1,sK0)),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f8,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f24,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(ennf_transformation,[],[f8])).
% 2.94/1.00  
% 2.94/1.00  fof(f54,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f24])).
% 2.94/1.00  
% 2.94/1.00  fof(f14,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f31,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.94/1.00    inference(ennf_transformation,[],[f14])).
% 2.94/1.00  
% 2.94/1.00  fof(f32,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/1.00    inference(flattening,[],[f31])).
% 2.94/1.00  
% 2.94/1.00  fof(f63,plain,(
% 2.94/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f32])).
% 2.94/1.00  
% 2.94/1.00  fof(f7,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f19,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.94/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.94/1.00  
% 2.94/1.00  fof(f23,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(ennf_transformation,[],[f19])).
% 2.94/1.00  
% 2.94/1.00  fof(f53,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f23])).
% 2.94/1.00  
% 2.94/1.00  fof(f11,axiom,(
% 2.94/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f27,plain,(
% 2.94/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.94/1.00    inference(ennf_transformation,[],[f11])).
% 2.94/1.00  
% 2.94/1.00  fof(f28,plain,(
% 2.94/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.94/1.00    inference(flattening,[],[f27])).
% 2.94/1.00  
% 2.94/1.00  fof(f40,plain,(
% 2.94/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.94/1.00    inference(nnf_transformation,[],[f28])).
% 2.94/1.00  
% 2.94/1.00  fof(f59,plain,(
% 2.94/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f40])).
% 2.94/1.00  
% 2.94/1.00  fof(f81,plain,(
% 2.94/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.94/1.00    inference(equality_resolution,[],[f59])).
% 2.94/1.00  
% 2.94/1.00  fof(f6,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f22,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(ennf_transformation,[],[f6])).
% 2.94/1.00  
% 2.94/1.00  fof(f52,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f22])).
% 2.94/1.00  
% 2.94/1.00  fof(f73,plain,(
% 2.94/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f5,axiom,(
% 2.94/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f51,plain,(
% 2.94/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f5])).
% 2.94/1.00  
% 2.94/1.00  fof(f75,plain,(
% 2.94/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.94/1.00    inference(definition_unfolding,[],[f51,f62])).
% 2.94/1.00  
% 2.94/1.00  fof(f2,axiom,(
% 2.94/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f37,plain,(
% 2.94/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/1.00    inference(nnf_transformation,[],[f2])).
% 2.94/1.00  
% 2.94/1.00  fof(f38,plain,(
% 2.94/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/1.00    inference(flattening,[],[f37])).
% 2.94/1.00  
% 2.94/1.00  fof(f46,plain,(
% 2.94/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.94/1.00    inference(cnf_transformation,[],[f38])).
% 2.94/1.00  
% 2.94/1.00  fof(f79,plain,(
% 2.94/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.94/1.00    inference(equality_resolution,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f1,axiom,(
% 2.94/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f20,plain,(
% 2.94/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.94/1.00    inference(ennf_transformation,[],[f1])).
% 2.94/1.00  
% 2.94/1.00  fof(f44,plain,(
% 2.94/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f20])).
% 2.94/1.00  
% 2.94/1.00  fof(f3,axiom,(
% 2.94/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f18,plain,(
% 2.94/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.94/1.00    inference(unused_predicate_definition_removal,[],[f3])).
% 2.94/1.00  
% 2.94/1.00  fof(f21,plain,(
% 2.94/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.94/1.00    inference(ennf_transformation,[],[f18])).
% 2.94/1.00  
% 2.94/1.00  fof(f48,plain,(
% 2.94/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f21])).
% 2.94/1.00  
% 2.94/1.00  fof(f45,plain,(
% 2.94/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f38])).
% 2.94/1.00  
% 2.94/1.00  fof(f4,axiom,(
% 2.94/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f49,plain,(
% 2.94/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.94/1.00    inference(cnf_transformation,[],[f4])).
% 2.94/1.00  
% 2.94/1.00  fof(f74,plain,(
% 2.94/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.94/1.00    inference(definition_unfolding,[],[f49,f62])).
% 2.94/1.00  
% 2.94/1.00  cnf(c_16,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.94/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | ~ v1_funct_1(X3) ),
% 2.94/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_969,plain,
% 2.94/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.94/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.94/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.94/1.00      | v1_funct_1(X0) != iProver_top
% 2.94/1.00      | v1_funct_1(X3) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_12,plain,
% 2.94/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | X3 = X2 ),
% 2.94/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_22,negated_conjecture,
% 2.94/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.94/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_404,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | X3 = X0
% 2.94/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.94/1.00      | k6_partfun1(sK0) != X3
% 2.94/1.00      | sK0 != X2
% 2.94/1.00      | sK0 != X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_405,plain,
% 2.94/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.94/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.94/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_404]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_13,plain,
% 2.94/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.94/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_413,plain,
% 2.94/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.94/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.94/1.01      inference(forward_subsumption_resolution,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_405,c_13]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_955,plain,
% 2.94/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.94/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2605,plain,
% 2.94/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.94/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.94/1.01      | v1_funct_1(sK2) != iProver_top
% 2.94/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_969,c_955]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_28,negated_conjecture,
% 2.94/1.01      ( v1_funct_1(sK2) ),
% 2.94/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_29,plain,
% 2.94/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_26,negated_conjecture,
% 2.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.94/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_31,plain,
% 2.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_25,negated_conjecture,
% 2.94/1.01      ( v1_funct_1(sK3) ),
% 2.94/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_32,plain,
% 2.94/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_23,negated_conjecture,
% 2.94/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.94/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_34,plain,
% 2.94/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2766,plain,
% 2.94/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.94/1.01      inference(global_propositional_subsumption,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_2605,c_29,c_31,c_32,c_34]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_20,plain,
% 2.94/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.01      | ~ v1_funct_2(X3,X4,X1)
% 2.94/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.01      | ~ v1_funct_1(X0)
% 2.94/1.01      | ~ v1_funct_1(X3)
% 2.94/1.01      | v2_funct_1(X3)
% 2.94/1.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.94/1.01      | k1_xboole_0 = X2 ),
% 2.94/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_966,plain,
% 2.94/1.01      ( k1_xboole_0 = X0
% 2.94/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.94/1.01      | v1_funct_2(X3,X4,X2) != iProver_top
% 2.94/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 2.94/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.94/1.01      | v1_funct_1(X1) != iProver_top
% 2.94/1.01      | v1_funct_1(X3) != iProver_top
% 2.94/1.01      | v2_funct_1(X3) = iProver_top
% 2.94/1.01      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2793,plain,
% 2.94/1.01      ( sK0 = k1_xboole_0
% 2.94/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.94/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.94/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.94/1.01      | v1_funct_1(sK2) != iProver_top
% 2.94/1.01      | v1_funct_1(sK3) != iProver_top
% 2.94/1.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.94/1.01      | v2_funct_1(sK2) = iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_2766,c_966]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_27,negated_conjecture,
% 2.94/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_30,plain,
% 2.94/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_24,negated_conjecture,
% 2.94/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.94/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_33,plain,
% 2.94/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_965,plain,
% 2.94/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_10,plain,
% 2.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.94/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_971,plain,
% 2.94/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.94/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1993,plain,
% 2.94/1.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_965,c_971]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_18,plain,
% 2.94/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.94/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.94/1.01      | ~ v1_funct_2(X3,X1,X0)
% 2.94/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.01      | ~ v1_funct_1(X2)
% 2.94/1.01      | ~ v1_funct_1(X3)
% 2.94/1.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_417,plain,
% 2.94/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.01      | ~ v1_funct_2(X3,X2,X1)
% 2.94/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.01      | ~ v1_funct_1(X0)
% 2.94/1.01      | ~ v1_funct_1(X3)
% 2.94/1.01      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.94/1.01      | k2_relset_1(X1,X2,X0) = X2
% 2.94/1.01      | k6_partfun1(X2) != k6_partfun1(sK0)
% 2.94/1.01      | sK0 != X2 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_418,plain,
% 2.94/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 2.94/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 2.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.94/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.94/1.01      | ~ v1_funct_1(X0)
% 2.94/1.01      | ~ v1_funct_1(X2)
% 2.94/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.94/1.01      | k2_relset_1(X1,sK0,X0) = sK0
% 2.94/1.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_417]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_490,plain,
% 2.94/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 2.94/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 2.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.94/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.94/1.01      | ~ v1_funct_1(X0)
% 2.94/1.01      | ~ v1_funct_1(X2)
% 2.94/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.94/1.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.94/1.01      inference(equality_resolution_simp,[status(thm)],[c_418]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_954,plain,
% 2.94/1.01      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.94/1.01      | k2_relset_1(X0,sK0,X2) = sK0
% 2.94/1.01      | v1_funct_2(X2,X0,sK0) != iProver_top
% 2.94/1.01      | v1_funct_2(X1,sK0,X0) != iProver_top
% 2.94/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.94/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.94/1.01      | v1_funct_1(X2) != iProver_top
% 2.94/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1658,plain,
% 2.94/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.94/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.94/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.94/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.94/1.01      | v1_funct_1(sK2) != iProver_top
% 2.94/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.94/1.01      inference(equality_resolution,[status(thm)],[c_954]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1790,plain,
% 2.94/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.94/1.01      inference(global_propositional_subsumption,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_1658,c_29,c_30,c_31,c_32,c_33,c_34]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2008,plain,
% 2.94/1.01      ( k2_relat_1(sK3) = sK0 ),
% 2.94/1.01      inference(light_normalisation,[status(thm)],[c_1993,c_1790]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_9,plain,
% 2.94/1.01      ( v5_relat_1(X0,X1)
% 2.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.94/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_14,plain,
% 2.94/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.94/1.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.94/1.01      | ~ v1_relat_1(X0) ),
% 2.94/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_322,plain,
% 2.94/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.94/1.01      | ~ v1_relat_1(X0)
% 2.94/1.01      | X0 != X1
% 2.94/1.01      | k2_relat_1(X0) != X3 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_323,plain,
% 2.94/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.94/1.01      | ~ v1_relat_1(X0) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_322]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_8,plain,
% 2.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.01      | v1_relat_1(X0) ),
% 2.94/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_333,plain,
% 2.94/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.94/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_323,c_8]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_21,negated_conjecture,
% 2.94/1.01      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.94/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_348,plain,
% 2.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.94/1.01      | ~ v2_funct_1(sK2)
% 2.94/1.01      | k2_relat_1(X0) != sK0
% 2.94/1.01      | sK3 != X0 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_333,c_21]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_349,plain,
% 2.94/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.94/1.01      | ~ v2_funct_1(sK2)
% 2.94/1.01      | k2_relat_1(sK3) != sK0 ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_348]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_600,plain,
% 2.94/1.01      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.94/1.01      inference(splitting,
% 2.94/1.01                [splitting(split),new_symbols(definition,[])],
% 2.94/1.01                [c_349]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_957,plain,
% 2.94/1.01      ( k2_relat_1(sK3) != sK0
% 2.94/1.01      | v2_funct_1(sK2) != iProver_top
% 2.94/1.01      | sP0_iProver_split = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2141,plain,
% 2.94/1.01      ( sK0 != sK0
% 2.94/1.01      | v2_funct_1(sK2) != iProver_top
% 2.94/1.01      | sP0_iProver_split = iProver_top ),
% 2.94/1.01      inference(demodulation,[status(thm)],[c_2008,c_957]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2142,plain,
% 2.94/1.01      ( v2_funct_1(sK2) != iProver_top
% 2.94/1.01      | sP0_iProver_split = iProver_top ),
% 2.94/1.01      inference(equality_resolution_simp,[status(thm)],[c_2141]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_599,plain,
% 2.94/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.94/1.01      | ~ sP0_iProver_split ),
% 2.94/1.01      inference(splitting,
% 2.94/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.94/1.01                [c_349]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_958,plain,
% 2.94/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 2.94/1.01      | sP0_iProver_split != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2140,plain,
% 2.94/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.94/1.01      | sP0_iProver_split != iProver_top ),
% 2.94/1.01      inference(demodulation,[status(thm)],[c_2008,c_958]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2158,plain,
% 2.94/1.01      ( sP0_iProver_split != iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_965,c_2140]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2973,plain,
% 2.94/1.01      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 2.94/1.01      inference(global_propositional_subsumption,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_2793,c_29,c_30,c_31,c_32,c_33,c_34,c_2142,c_2158]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2974,plain,
% 2.94/1.01      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 2.94/1.01      inference(renaming,[status(thm)],[c_2973]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_6,plain,
% 2.94/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.94/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_972,plain,
% 2.94/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2979,plain,
% 2.94/1.01      ( sK0 = k1_xboole_0 ),
% 2.94/1.01      inference(forward_subsumption_resolution,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_2974,c_972]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_962,plain,
% 2.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2987,plain,
% 2.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.94/1.01      inference(demodulation,[status(thm)],[c_2979,c_962]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2,plain,
% 2.94/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2995,plain,
% 2.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/1.01      inference(demodulation,[status(thm)],[c_2987,c_2]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_603,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1594,plain,
% 2.94/1.01      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_603]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2298,plain,
% 2.94/1.01      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1594]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2299,plain,
% 2.94/1.01      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_2298]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_608,plain,
% 2.94/1.01      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.94/1.01      theory(equality) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1913,plain,
% 2.94/1.01      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_608]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1914,plain,
% 2.94/1.01      ( sK2 != X0
% 2.94/1.01      | v2_funct_1(X0) != iProver_top
% 2.94/1.01      | v2_funct_1(sK2) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1916,plain,
% 2.94/1.01      ( sK2 != k1_xboole_0
% 2.94/1.01      | v2_funct_1(sK2) = iProver_top
% 2.94/1.01      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1914]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1475,plain,
% 2.94/1.01      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_603]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1476,plain,
% 2.94/1.01      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 2.94/1.01      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 2.94/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1475]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_602,plain,( X0 = X0 ),theory(equality) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1326,plain,
% 2.94/1.01      ( sK2 = sK2 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_602]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_0,plain,
% 2.94/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_4,plain,
% 2.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_288,plain,
% 2.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.94/1.01      | X0 != X2
% 2.94/1.01      | k1_xboole_0 != X1
% 2.94/1.01      | k1_xboole_0 = X2 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_289,plain,
% 2.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_288]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1280,plain,
% 2.94/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_289]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1283,plain,
% 2.94/1.01      ( k1_xboole_0 = sK2
% 2.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1168,plain,
% 2.94/1.01      ( v2_funct_1(X0)
% 2.94/1.01      | ~ v2_funct_1(k6_partfun1(X1))
% 2.94/1.01      | X0 != k6_partfun1(X1) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_608]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1169,plain,
% 2.94/1.01      ( X0 != k6_partfun1(X1)
% 2.94/1.01      | v2_funct_1(X0) = iProver_top
% 2.94/1.01      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_1168]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1171,plain,
% 2.94/1.01      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 2.94/1.01      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 2.94/1.01      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1169]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_86,plain,
% 2.94/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_3,plain,
% 2.94/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.94/1.01      | k1_xboole_0 = X0
% 2.94/1.01      | k1_xboole_0 = X1 ),
% 2.94/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_85,plain,
% 2.94/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.94/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_5,plain,
% 2.94/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_79,plain,
% 2.94/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_81,plain,
% 2.94/1.01      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_79]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(contradiction,plain,
% 2.94/1.01      ( $false ),
% 2.94/1.01      inference(minisat,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_2995,c_2299,c_2158,c_2142,c_1916,c_1476,c_1326,c_1283,
% 2.94/1.01                 c_1171,c_86,c_85,c_5,c_81]) ).
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.01  
% 2.94/1.01  ------                               Statistics
% 2.94/1.01  
% 2.94/1.01  ------ General
% 2.94/1.01  
% 2.94/1.01  abstr_ref_over_cycles:                  0
% 2.94/1.01  abstr_ref_under_cycles:                 0
% 2.94/1.01  gc_basic_clause_elim:                   0
% 2.94/1.01  forced_gc_time:                         0
% 2.94/1.01  parsing_time:                           0.009
% 2.94/1.01  unif_index_cands_time:                  0.
% 2.94/1.01  unif_index_add_time:                    0.
% 2.94/1.01  orderings_time:                         0.
% 2.94/1.01  out_proof_time:                         0.011
% 2.94/1.01  total_time:                             0.151
% 2.94/1.01  num_of_symbols:                         52
% 2.94/1.01  num_of_terms:                           4699
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing
% 2.94/1.01  
% 2.94/1.01  num_of_splits:                          1
% 2.94/1.01  num_of_split_atoms:                     1
% 2.94/1.01  num_of_reused_defs:                     0
% 2.94/1.01  num_eq_ax_congr_red:                    10
% 2.94/1.01  num_of_sem_filtered_clauses:            1
% 2.94/1.01  num_of_subtypes:                        0
% 2.94/1.01  monotx_restored_types:                  0
% 2.94/1.01  sat_num_of_epr_types:                   0
% 2.94/1.01  sat_num_of_non_cyclic_types:            0
% 2.94/1.01  sat_guarded_non_collapsed_types:        0
% 2.94/1.01  num_pure_diseq_elim:                    0
% 2.94/1.01  simp_replaced_by:                       0
% 2.94/1.01  res_preprocessed:                       122
% 2.94/1.01  prep_upred:                             0
% 2.94/1.01  prep_unflattend:                        19
% 2.94/1.01  smt_new_axioms:                         0
% 2.94/1.01  pred_elim_cands:                        4
% 2.94/1.01  pred_elim:                              5
% 2.94/1.01  pred_elim_cl:                           7
% 2.94/1.01  pred_elim_cycles:                       7
% 2.94/1.01  merged_defs:                            0
% 2.94/1.01  merged_defs_ncl:                        0
% 2.94/1.01  bin_hyper_res:                          0
% 2.94/1.01  prep_cycles:                            4
% 2.94/1.01  pred_elim_time:                         0.005
% 2.94/1.01  splitting_time:                         0.
% 2.94/1.01  sem_filter_time:                        0.
% 2.94/1.01  monotx_time:                            0.
% 2.94/1.01  subtype_inf_time:                       0.
% 2.94/1.01  
% 2.94/1.01  ------ Problem properties
% 2.94/1.01  
% 2.94/1.01  clauses:                                23
% 2.94/1.01  conjectures:                            6
% 2.94/1.01  epr:                                    4
% 2.94/1.01  horn:                                   21
% 2.94/1.01  ground:                                 9
% 2.94/1.01  unary:                                  11
% 2.94/1.01  binary:                                 4
% 2.94/1.01  lits:                                   68
% 2.94/1.01  lits_eq:                                15
% 2.94/1.01  fd_pure:                                0
% 2.94/1.01  fd_pseudo:                              0
% 2.94/1.01  fd_cond:                                3
% 2.94/1.01  fd_pseudo_cond:                         0
% 2.94/1.01  ac_symbols:                             0
% 2.94/1.01  
% 2.94/1.01  ------ Propositional Solver
% 2.94/1.01  
% 2.94/1.01  prop_solver_calls:                      26
% 2.94/1.01  prop_fast_solver_calls:                 867
% 2.94/1.01  smt_solver_calls:                       0
% 2.94/1.01  smt_fast_solver_calls:                  0
% 2.94/1.01  prop_num_of_clauses:                    1105
% 2.94/1.01  prop_preprocess_simplified:             4107
% 2.94/1.01  prop_fo_subsumed:                       22
% 2.94/1.01  prop_solver_time:                       0.
% 2.94/1.01  smt_solver_time:                        0.
% 2.94/1.01  smt_fast_solver_time:                   0.
% 2.94/1.01  prop_fast_solver_time:                  0.
% 2.94/1.01  prop_unsat_core_time:                   0.
% 2.94/1.01  
% 2.94/1.01  ------ QBF
% 2.94/1.01  
% 2.94/1.01  qbf_q_res:                              0
% 2.94/1.01  qbf_num_tautologies:                    0
% 2.94/1.01  qbf_prep_cycles:                        0
% 2.94/1.01  
% 2.94/1.01  ------ BMC1
% 2.94/1.01  
% 2.94/1.01  bmc1_current_bound:                     -1
% 2.94/1.01  bmc1_last_solved_bound:                 -1
% 2.94/1.01  bmc1_unsat_core_size:                   -1
% 2.94/1.01  bmc1_unsat_core_parents_size:           -1
% 2.94/1.01  bmc1_merge_next_fun:                    0
% 2.94/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.94/1.01  
% 2.94/1.01  ------ Instantiation
% 2.94/1.01  
% 2.94/1.01  inst_num_of_clauses:                    369
% 2.94/1.01  inst_num_in_passive:                    131
% 2.94/1.01  inst_num_in_active:                     198
% 2.94/1.01  inst_num_in_unprocessed:                40
% 2.94/1.01  inst_num_of_loops:                      210
% 2.94/1.01  inst_num_of_learning_restarts:          0
% 2.94/1.01  inst_num_moves_active_passive:          9
% 2.94/1.01  inst_lit_activity:                      0
% 2.94/1.01  inst_lit_activity_moves:                0
% 2.94/1.01  inst_num_tautologies:                   0
% 2.94/1.01  inst_num_prop_implied:                  0
% 2.94/1.01  inst_num_existing_simplified:           0
% 2.94/1.01  inst_num_eq_res_simplified:             0
% 2.94/1.01  inst_num_child_elim:                    0
% 2.94/1.01  inst_num_of_dismatching_blockings:      12
% 2.94/1.01  inst_num_of_non_proper_insts:           223
% 2.94/1.01  inst_num_of_duplicates:                 0
% 2.94/1.01  inst_inst_num_from_inst_to_res:         0
% 2.94/1.01  inst_dismatching_checking_time:         0.
% 2.94/1.01  
% 2.94/1.01  ------ Resolution
% 2.94/1.01  
% 2.94/1.01  res_num_of_clauses:                     0
% 2.94/1.01  res_num_in_passive:                     0
% 2.94/1.01  res_num_in_active:                      0
% 2.94/1.01  res_num_of_loops:                       126
% 2.94/1.01  res_forward_subset_subsumed:            13
% 2.94/1.01  res_backward_subset_subsumed:           0
% 2.94/1.01  res_forward_subsumed:                   0
% 2.94/1.01  res_backward_subsumed:                  0
% 2.94/1.01  res_forward_subsumption_resolution:     4
% 2.94/1.01  res_backward_subsumption_resolution:    0
% 2.94/1.01  res_clause_to_clause_subsumption:       99
% 2.94/1.01  res_orphan_elimination:                 0
% 2.94/1.01  res_tautology_del:                      13
% 2.94/1.01  res_num_eq_res_simplified:              1
% 2.94/1.01  res_num_sel_changes:                    0
% 2.94/1.01  res_moves_from_active_to_pass:          0
% 2.94/1.01  
% 2.94/1.01  ------ Superposition
% 2.94/1.01  
% 2.94/1.01  sup_time_total:                         0.
% 2.94/1.01  sup_time_generating:                    0.
% 2.94/1.01  sup_time_sim_full:                      0.
% 2.94/1.01  sup_time_sim_immed:                     0.
% 2.94/1.01  
% 2.94/1.01  sup_num_of_clauses:                     43
% 2.94/1.01  sup_num_in_active:                      25
% 2.94/1.01  sup_num_in_passive:                     18
% 2.94/1.01  sup_num_of_loops:                       40
% 2.94/1.01  sup_fw_superposition:                   19
% 2.94/1.01  sup_bw_superposition:                   13
% 2.94/1.01  sup_immediate_simplified:               11
% 2.94/1.01  sup_given_eliminated:                   1
% 2.94/1.01  comparisons_done:                       0
% 2.94/1.01  comparisons_avoided:                    0
% 2.94/1.01  
% 2.94/1.01  ------ Simplifications
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  sim_fw_subset_subsumed:                 0
% 2.94/1.01  sim_bw_subset_subsumed:                 0
% 2.94/1.01  sim_fw_subsumed:                        1
% 2.94/1.01  sim_bw_subsumed:                        1
% 2.94/1.01  sim_fw_subsumption_res:                 1
% 2.94/1.01  sim_bw_subsumption_res:                 0
% 2.94/1.01  sim_tautology_del:                      0
% 2.94/1.01  sim_eq_tautology_del:                   3
% 2.94/1.01  sim_eq_res_simp:                        1
% 2.94/1.01  sim_fw_demodulated:                     6
% 2.94/1.01  sim_bw_demodulated:                     14
% 2.94/1.01  sim_light_normalised:                   5
% 2.94/1.01  sim_joinable_taut:                      0
% 2.94/1.01  sim_joinable_simp:                      0
% 2.94/1.01  sim_ac_normalised:                      0
% 2.94/1.01  sim_smt_subsumption:                    0
% 2.94/1.01  
%------------------------------------------------------------------------------
