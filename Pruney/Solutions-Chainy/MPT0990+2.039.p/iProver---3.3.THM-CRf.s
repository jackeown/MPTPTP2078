%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:04 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  162 (1041 expanded)
%              Number of clauses        :   93 ( 285 expanded)
%              Number of leaves         :   19 ( 276 expanded)
%              Depth                    :   19
%              Number of atoms          :  669 (9097 expanded)
%              Number of equality atoms :  319 (3306 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f33])).

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
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_0,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1161,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_382,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_390,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_382,c_16])).

cnf(c_1133,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1382,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1871,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1133,c_34,c_32,c_31,c_29,c_390,c_1382])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1144,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4054,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1144])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4093,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4054,c_35,c_36,c_37])).

cnf(c_4094,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4093])).

cnf(c_4097,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_4094])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_651,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_676,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_652,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1256,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_1257,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_4230,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4097,c_38,c_39,c_40,c_25,c_676,c_1257])).

cnf(c_4234,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_4230])).

cnf(c_1140,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2087,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1158])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1159,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2559,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_1159])).

cnf(c_2624,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2559,c_38])).

cnf(c_4237,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_4234,c_2624])).

cnf(c_1137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1146,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3299,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1146])).

cnf(c_3444,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3299,c_38])).

cnf(c_3445,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3444])).

cnf(c_3453,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_3445])).

cnf(c_3454,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3453,c_1871])).

cnf(c_3840,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3454,c_35])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1160,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4061,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3840,c_1160])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1156,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2233,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1137,c_1156])).

cnf(c_2234,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2233,c_28])).

cnf(c_2232,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1140,c_1156])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_394,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_395,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_479,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_395])).

cnf(c_1132,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1608,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1132])).

cnf(c_1974,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1608,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_2235,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2232,c_1974])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1150,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2810,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1150])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1157,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2369,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1140,c_1157])).

cnf(c_2813,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2810,c_2369])).

cnf(c_2860,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2813,c_39,c_25,c_676,c_1257])).

cnf(c_4062,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4061,c_2234,c_2235,c_2860])).

cnf(c_4063,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4062])).

cnf(c_1271,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1520,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1521,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_1706,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2081,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_2082,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_5115,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4063,c_35,c_37,c_38,c_40,c_1521,c_2082,c_4234])).

cnf(c_5807,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4237,c_4237,c_5115])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5807,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.52/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/1.00  
% 3.52/1.00  ------  iProver source info
% 3.52/1.00  
% 3.52/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.52/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/1.00  git: non_committed_changes: false
% 3.52/1.00  git: last_make_outside_of_git: false
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    ""
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         true
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     num_symb
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       true
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     true
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_input_bw                          []
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  ------ Parsing...
% 3.52/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/1.00  ------ Proving...
% 3.52/1.00  ------ Problem Properties 
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  clauses                                 34
% 3.52/1.00  conjectures                             11
% 3.52/1.00  EPR                                     7
% 3.52/1.00  Horn                                    28
% 3.52/1.00  unary                                   13
% 3.52/1.00  binary                                  4
% 3.52/1.00  lits                                    123
% 3.52/1.00  lits eq                                 31
% 3.52/1.00  fd_pure                                 0
% 3.52/1.00  fd_pseudo                               0
% 3.52/1.00  fd_cond                                 5
% 3.52/1.00  fd_pseudo_cond                          1
% 3.52/1.00  AC symbols                              0
% 3.52/1.00  
% 3.52/1.00  ------ Schedule dynamic 5 is on 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  Current options:
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    ""
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         true
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     none
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       false
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     true
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_input_bw                          []
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ Proving...
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS status Theorem for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  fof(f1,axiom,(
% 3.52/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f44,plain,(
% 3.52/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f1])).
% 3.52/1.00  
% 3.52/1.00  fof(f12,axiom,(
% 3.52/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f62,plain,(
% 3.52/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f12])).
% 3.52/1.00  
% 3.52/1.00  fof(f80,plain,(
% 3.52/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f44,f62])).
% 3.52/1.00  
% 3.52/1.00  fof(f7,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f25,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.52/1.00    inference(ennf_transformation,[],[f7])).
% 3.52/1.00  
% 3.52/1.00  fof(f26,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(flattening,[],[f25])).
% 3.52/1.00  
% 3.52/1.00  fof(f39,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(nnf_transformation,[],[f26])).
% 3.52/1.00  
% 3.52/1.00  fof(f50,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f39])).
% 3.52/1.00  
% 3.52/1.00  fof(f15,conjecture,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f16,negated_conjecture,(
% 3.52/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.52/1.00    inference(negated_conjecture,[],[f15])).
% 3.52/1.00  
% 3.52/1.00  fof(f37,plain,(
% 3.52/1.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f16])).
% 3.52/1.00  
% 3.52/1.00  fof(f38,plain,(
% 3.52/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f37])).
% 3.52/1.00  
% 3.52/1.00  fof(f42,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f41,plain,(
% 3.52/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f43,plain,(
% 3.52/1.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 3.52/1.00  
% 3.52/1.00  fof(f75,plain,(
% 3.52/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f10,axiom,(
% 3.52/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f17,plain,(
% 3.52/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.52/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.52/1.00  
% 3.52/1.00  fof(f60,plain,(
% 3.52/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f17])).
% 3.52/1.00  
% 3.52/1.00  fof(f68,plain,(
% 3.52/1.00    v1_funct_1(sK2)),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f70,plain,(
% 3.52/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f71,plain,(
% 3.52/1.00    v1_funct_1(sK3)),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f73,plain,(
% 3.52/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f9,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f29,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.52/1.00    inference(ennf_transformation,[],[f9])).
% 3.52/1.00  
% 3.52/1.00  fof(f30,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.52/1.00    inference(flattening,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f59,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f30])).
% 3.52/1.00  
% 3.52/1.00  fof(f74,plain,(
% 3.52/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f14,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f35,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.52/1.00    inference(ennf_transformation,[],[f14])).
% 3.52/1.00  
% 3.52/1.00  fof(f36,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.52/1.00    inference(flattening,[],[f35])).
% 3.52/1.00  
% 3.52/1.00  fof(f66,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f36])).
% 3.52/1.00  
% 3.52/1.00  fof(f69,plain,(
% 3.52/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f72,plain,(
% 3.52/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f77,plain,(
% 3.52/1.00    k1_xboole_0 != sK0),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f4,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f22,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f4])).
% 3.52/1.00  
% 3.52/1.00  fof(f47,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f22])).
% 3.52/1.00  
% 3.52/1.00  fof(f3,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f20,plain,(
% 3.52/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f3])).
% 3.52/1.00  
% 3.52/1.00  fof(f21,plain,(
% 3.52/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f20])).
% 3.52/1.00  
% 3.52/1.00  fof(f46,plain,(
% 3.52/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f21])).
% 3.52/1.00  
% 3.52/1.00  fof(f11,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f31,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.52/1.00    inference(ennf_transformation,[],[f11])).
% 3.52/1.00  
% 3.52/1.00  fof(f32,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.52/1.00    inference(flattening,[],[f31])).
% 3.52/1.00  
% 3.52/1.00  fof(f61,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f2,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f18,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f2])).
% 3.52/1.00  
% 3.52/1.00  fof(f19,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f18])).
% 3.52/1.00  
% 3.52/1.00  fof(f45,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f19])).
% 3.52/1.00  
% 3.52/1.00  fof(f81,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f45,f62])).
% 3.52/1.00  
% 3.52/1.00  fof(f6,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f24,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f6])).
% 3.52/1.00  
% 3.52/1.00  fof(f49,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f24])).
% 3.52/1.00  
% 3.52/1.00  fof(f13,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f33,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f34,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f33])).
% 3.52/1.00  
% 3.52/1.00  fof(f63,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f34])).
% 3.52/1.00  
% 3.52/1.00  fof(f8,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f27,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f8])).
% 3.52/1.00  
% 3.52/1.00  fof(f28,plain,(
% 3.52/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(flattening,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f40,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(nnf_transformation,[],[f28])).
% 3.52/1.00  
% 3.52/1.00  fof(f52,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f40])).
% 3.52/1.00  
% 3.52/1.00  fof(f5,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f23,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f5])).
% 3.52/1.00  
% 3.52/1.00  fof(f48,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f23])).
% 3.52/1.00  
% 3.52/1.00  fof(f79,plain,(
% 3.52/1.00    k2_funct_1(sK2) != sK3),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  cnf(c_0,plain,
% 3.52/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1161,plain,
% 3.52/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7,plain,
% 3.52/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.52/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | X3 = X2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_27,negated_conjecture,
% 3.52/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_381,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | X3 = X0
% 3.52/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.52/1.00      | k6_partfun1(sK0) != X3
% 3.52/1.00      | sK0 != X2
% 3.52/1.00      | sK0 != X1 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_382,plain,
% 3.52/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.52/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.52/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_381]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_16,plain,
% 3.52/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_390,plain,
% 3.52/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.52/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.52/1.00      inference(forward_subsumption_resolution,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_382,c_16]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1133,plain,
% 3.52/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.52/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_34,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK2) ),
% 3.52/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_32,negated_conjecture,
% 3.52/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_31,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK3) ),
% 3.52/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_29,negated_conjecture,
% 3.52/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_14,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.52/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X3) ),
% 3.52/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1382,plain,
% 3.52/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v1_funct_1(sK2) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1871,plain,
% 3.53/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_1133,c_34,c_32,c_31,c_29,c_390,c_1382]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_28,negated_conjecture,
% 3.53/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.53/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_20,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v1_funct_1(X3)
% 3.53/1.00      | v2_funct_1(X0)
% 3.53/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.53/1.00      | k2_relset_1(X4,X1,X3) != X1
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1144,plain,
% 3.53/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.53/1.00      | k1_xboole_0 = X3
% 3.53/1.00      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.53/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.53/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.53/1.00      | v1_funct_1(X4) != iProver_top
% 3.53/1.00      | v1_funct_1(X2) != iProver_top
% 3.53/1.00      | v2_funct_1(X4) = iProver_top
% 3.53/1.00      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4054,plain,
% 3.53/1.00      ( k1_xboole_0 = X0
% 3.53/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.53/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.53/1.00      | v1_funct_1(X1) != iProver_top
% 3.53/1.00      | v1_funct_1(sK2) != iProver_top
% 3.53/1.00      | v2_funct_1(X1) = iProver_top
% 3.53/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_28,c_1144]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_35,plain,
% 3.53/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_33,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_36,plain,
% 3.53/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_37,plain,
% 3.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4093,plain,
% 3.53/1.00      ( v1_funct_1(X1) != iProver_top
% 3.53/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.53/1.00      | k1_xboole_0 = X0
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.53/1.00      | v2_funct_1(X1) = iProver_top
% 3.53/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4054,c_35,c_36,c_37]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4094,plain,
% 3.53/1.00      ( k1_xboole_0 = X0
% 3.53/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.53/1.00      | v1_funct_1(X1) != iProver_top
% 3.53/1.00      | v2_funct_1(X1) = iProver_top
% 3.53/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_4093]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4097,plain,
% 3.53/1.00      ( sK0 = k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.53/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1871,c_4094]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_38,plain,
% 3.53/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_30,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_39,plain,
% 3.53/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_40,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_25,negated_conjecture,
% 3.53/1.00      ( k1_xboole_0 != sK0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_651,plain,( X0 = X0 ),theory(equality) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_676,plain,
% 3.53/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_651]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_652,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1256,plain,
% 3.53/1.00      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_652]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1257,plain,
% 3.53/1.00      ( sK0 != k1_xboole_0
% 3.53/1.00      | k1_xboole_0 = sK0
% 3.53/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_1256]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4230,plain,
% 3.53/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.53/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4097,c_38,c_39,c_40,c_25,c_676,c_1257]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4234,plain,
% 3.53/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1161,c_4230]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1140,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | v1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1158,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.53/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2087,plain,
% 3.53/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1140,c_1158]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2,plain,
% 3.53/1.00      ( ~ v1_relat_1(X0)
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v2_funct_1(X0)
% 3.53/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1159,plain,
% 3.53/1.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.53/1.00      | v1_relat_1(X0) != iProver_top
% 3.53/1.00      | v1_funct_1(X0) != iProver_top
% 3.53/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2559,plain,
% 3.53/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2087,c_1159]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2624,plain,
% 3.53/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.53/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2559,c_38]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4237,plain,
% 3.53/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4234,c_2624]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1137,plain,
% 3.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v1_funct_1(X3)
% 3.53/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1146,plain,
% 3.53/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.53/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.53/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.53/1.00      | v1_funct_1(X5) != iProver_top
% 3.53/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3299,plain,
% 3.53/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.53/1.00      | v1_funct_1(X2) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1140,c_1146]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3444,plain,
% 3.53/1.00      ( v1_funct_1(X2) != iProver_top
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.53/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_3299,c_38]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3445,plain,
% 3.53/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.53/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_3444]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3453,plain,
% 3.53/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.53/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1137,c_3445]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3454,plain,
% 3.53/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.53/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_3453,c_1871]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3840,plain,
% 3.53/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_3454,c_35]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1,plain,
% 3.53/1.00      ( ~ v1_relat_1(X0)
% 3.53/1.00      | ~ v1_relat_1(X1)
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v2_funct_1(X1)
% 3.53/1.00      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.53/1.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.53/1.00      | k2_funct_1(X1) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1160,plain,
% 3.53/1.00      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.53/1.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.53/1.00      | k2_funct_1(X1) = X0
% 3.53/1.00      | v1_relat_1(X0) != iProver_top
% 3.53/1.00      | v1_relat_1(X1) != iProver_top
% 3.53/1.00      | v1_funct_1(X0) != iProver_top
% 3.53/1.00      | v1_funct_1(X1) != iProver_top
% 3.53/1.00      | v2_funct_1(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4061,plain,
% 3.53/1.00      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.53/1.00      | k2_funct_1(sK3) = sK2
% 3.53/1.00      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.53/1.00      | v1_relat_1(sK3) != iProver_top
% 3.53/1.00      | v1_relat_1(sK2) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v1_funct_1(sK2) != iProver_top
% 3.53/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3840,c_1160]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1156,plain,
% 3.53/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2233,plain,
% 3.53/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1137,c_1156]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2234,plain,
% 3.53/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2233,c_28]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2232,plain,
% 3.53/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1140,c_1156]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_18,plain,
% 3.53/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.53/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.53/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.53/1.00      | ~ v1_funct_1(X2)
% 3.53/1.00      | ~ v1_funct_1(X3)
% 3.53/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_394,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.53/1.00      | ~ v1_funct_1(X3)
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.53/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.53/1.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.53/1.00      | sK0 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_395,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.53/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.53/1.00      | ~ v1_funct_1(X2)
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.53/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 3.53/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_479,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.53/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v1_funct_1(X2)
% 3.53/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.53/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_395]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1132,plain,
% 3.53/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.53/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 3.53/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.53/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.53/1.00      | v1_funct_1(X2) != iProver_top
% 3.53/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1608,plain,
% 3.53/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.53/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.53/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.53/1.00      inference(equality_resolution,[status(thm)],[c_1132]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1974,plain,
% 3.53/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_1608,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2235,plain,
% 3.53/1.00      ( k2_relat_1(sK3) = sK0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2232,c_1974]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_13,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1150,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.53/1.00      | k1_xboole_0 = X1
% 3.53/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2810,plain,
% 3.53/1.00      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.53/1.00      | sK0 = k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1140,c_1150]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1157,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2369,plain,
% 3.53/1.00      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1140,c_1157]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2813,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = sK1
% 3.53/1.00      | sK0 = k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2810,c_2369]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2860,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = sK1 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2813,c_39,c_25,c_676,c_1257]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4062,plain,
% 3.53/1.00      ( k2_funct_1(sK3) = sK2
% 3.53/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.53/1.00      | sK1 != sK1
% 3.53/1.00      | v1_relat_1(sK3) != iProver_top
% 3.53/1.00      | v1_relat_1(sK2) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v1_funct_1(sK2) != iProver_top
% 3.53/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4061,c_2234,c_2235,c_2860]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4063,plain,
% 3.53/1.00      ( k2_funct_1(sK3) = sK2
% 3.53/1.00      | v1_relat_1(sK3) != iProver_top
% 3.53/1.00      | v1_relat_1(sK2) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v1_funct_1(sK2) != iProver_top
% 3.53/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_4062]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1271,plain,
% 3.53/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.53/1.00      | v1_relat_1(sK3) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1520,plain,
% 3.53/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.53/1.00      | v1_relat_1(sK3) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_1271]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1521,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.53/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1706,plain,
% 3.53/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.53/1.00      | v1_relat_1(sK2) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2081,plain,
% 3.53/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.53/1.00      | v1_relat_1(sK2) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_1706]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2082,plain,
% 3.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.53/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5115,plain,
% 3.53/1.00      ( k2_funct_1(sK3) = sK2 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4063,c_35,c_37,c_38,c_40,c_1521,c_2082,c_4234]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5807,plain,
% 3.53/1.00      ( k2_funct_1(sK2) = sK3 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_4237,c_4237,c_5115]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_23,negated_conjecture,
% 3.53/1.00      ( k2_funct_1(sK2) != sK3 ),
% 3.53/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(contradiction,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(minisat,[status(thm)],[c_5807,c_23]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ General
% 3.53/1.00  
% 3.53/1.00  abstr_ref_over_cycles:                  0
% 3.53/1.00  abstr_ref_under_cycles:                 0
% 3.53/1.00  gc_basic_clause_elim:                   0
% 3.53/1.00  forced_gc_time:                         0
% 3.53/1.00  parsing_time:                           0.009
% 3.53/1.00  unif_index_cands_time:                  0.
% 3.53/1.00  unif_index_add_time:                    0.
% 3.53/1.00  orderings_time:                         0.
% 3.53/1.00  out_proof_time:                         0.011
% 3.53/1.00  total_time:                             0.26
% 3.53/1.00  num_of_symbols:                         52
% 3.53/1.00  num_of_terms:                           9763
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing
% 3.53/1.00  
% 3.53/1.00  num_of_splits:                          0
% 3.53/1.00  num_of_split_atoms:                     0
% 3.53/1.00  num_of_reused_defs:                     0
% 3.53/1.00  num_eq_ax_congr_red:                    21
% 3.53/1.00  num_of_sem_filtered_clauses:            1
% 3.53/1.00  num_of_subtypes:                        0
% 3.53/1.00  monotx_restored_types:                  0
% 3.53/1.00  sat_num_of_epr_types:                   0
% 3.53/1.00  sat_num_of_non_cyclic_types:            0
% 3.53/1.00  sat_guarded_non_collapsed_types:        0
% 3.53/1.00  num_pure_diseq_elim:                    0
% 3.53/1.00  simp_replaced_by:                       0
% 3.53/1.00  res_preprocessed:                       164
% 3.53/1.00  prep_upred:                             0
% 3.53/1.00  prep_unflattend:                        12
% 3.53/1.00  smt_new_axioms:                         0
% 3.53/1.00  pred_elim_cands:                        5
% 3.53/1.00  pred_elim:                              1
% 3.53/1.00  pred_elim_cl:                           1
% 3.53/1.00  pred_elim_cycles:                       3
% 3.53/1.00  merged_defs:                            0
% 3.53/1.00  merged_defs_ncl:                        0
% 3.53/1.00  bin_hyper_res:                          0
% 3.53/1.00  prep_cycles:                            4
% 3.53/1.00  pred_elim_time:                         0.005
% 3.53/1.00  splitting_time:                         0.
% 3.53/1.00  sem_filter_time:                        0.
% 3.53/1.00  monotx_time:                            0.001
% 3.53/1.00  subtype_inf_time:                       0.
% 3.53/1.00  
% 3.53/1.00  ------ Problem properties
% 3.53/1.00  
% 3.53/1.00  clauses:                                34
% 3.53/1.00  conjectures:                            11
% 3.53/1.00  epr:                                    7
% 3.53/1.00  horn:                                   28
% 3.53/1.00  ground:                                 12
% 3.53/1.00  unary:                                  13
% 3.53/1.00  binary:                                 4
% 3.53/1.00  lits:                                   123
% 3.53/1.00  lits_eq:                                31
% 3.53/1.00  fd_pure:                                0
% 3.53/1.00  fd_pseudo:                              0
% 3.53/1.00  fd_cond:                                5
% 3.53/1.00  fd_pseudo_cond:                         1
% 3.53/1.00  ac_symbols:                             0
% 3.53/1.00  
% 3.53/1.00  ------ Propositional Solver
% 3.53/1.00  
% 3.53/1.00  prop_solver_calls:                      30
% 3.53/1.00  prop_fast_solver_calls:                 1505
% 3.53/1.00  smt_solver_calls:                       0
% 3.53/1.00  smt_fast_solver_calls:                  0
% 3.53/1.00  prop_num_of_clauses:                    2832
% 3.53/1.00  prop_preprocess_simplified:             7345
% 3.53/1.00  prop_fo_subsumed:                       65
% 3.53/1.00  prop_solver_time:                       0.
% 3.53/1.00  smt_solver_time:                        0.
% 3.53/1.00  smt_fast_solver_time:                   0.
% 3.53/1.00  prop_fast_solver_time:                  0.
% 3.53/1.00  prop_unsat_core_time:                   0.
% 3.53/1.00  
% 3.53/1.00  ------ QBF
% 3.53/1.00  
% 3.53/1.00  qbf_q_res:                              0
% 3.53/1.00  qbf_num_tautologies:                    0
% 3.53/1.00  qbf_prep_cycles:                        0
% 3.53/1.00  
% 3.53/1.00  ------ BMC1
% 3.53/1.00  
% 3.53/1.00  bmc1_current_bound:                     -1
% 3.53/1.00  bmc1_last_solved_bound:                 -1
% 3.53/1.00  bmc1_unsat_core_size:                   -1
% 3.53/1.00  bmc1_unsat_core_parents_size:           -1
% 3.53/1.00  bmc1_merge_next_fun:                    0
% 3.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation
% 3.53/1.00  
% 3.53/1.00  inst_num_of_clauses:                    815
% 3.53/1.00  inst_num_in_passive:                    69
% 3.53/1.00  inst_num_in_active:                     441
% 3.53/1.00  inst_num_in_unprocessed:                305
% 3.53/1.00  inst_num_of_loops:                      460
% 3.53/1.00  inst_num_of_learning_restarts:          0
% 3.53/1.00  inst_num_moves_active_passive:          16
% 3.53/1.00  inst_lit_activity:                      0
% 3.53/1.00  inst_lit_activity_moves:                0
% 3.53/1.00  inst_num_tautologies:                   0
% 3.53/1.00  inst_num_prop_implied:                  0
% 3.53/1.00  inst_num_existing_simplified:           0
% 3.53/1.00  inst_num_eq_res_simplified:             0
% 3.53/1.00  inst_num_child_elim:                    0
% 3.53/1.00  inst_num_of_dismatching_blockings:      239
% 3.53/1.00  inst_num_of_non_proper_insts:           746
% 3.53/1.00  inst_num_of_duplicates:                 0
% 3.53/1.00  inst_inst_num_from_inst_to_res:         0
% 3.53/1.00  inst_dismatching_checking_time:         0.
% 3.53/1.00  
% 3.53/1.00  ------ Resolution
% 3.53/1.00  
% 3.53/1.00  res_num_of_clauses:                     0
% 3.53/1.00  res_num_in_passive:                     0
% 3.53/1.00  res_num_in_active:                      0
% 3.53/1.00  res_num_of_loops:                       168
% 3.53/1.00  res_forward_subset_subsumed:            89
% 3.53/1.00  res_backward_subset_subsumed:           0
% 3.53/1.00  res_forward_subsumed:                   0
% 3.53/1.00  res_backward_subsumed:                  0
% 3.53/1.00  res_forward_subsumption_resolution:     2
% 3.53/1.00  res_backward_subsumption_resolution:    0
% 3.53/1.00  res_clause_to_clause_subsumption:       253
% 3.53/1.00  res_orphan_elimination:                 0
% 3.53/1.00  res_tautology_del:                      16
% 3.53/1.00  res_num_eq_res_simplified:              1
% 3.53/1.00  res_num_sel_changes:                    0
% 3.53/1.00  res_moves_from_active_to_pass:          0
% 3.53/1.00  
% 3.53/1.00  ------ Superposition
% 3.53/1.00  
% 3.53/1.00  sup_time_total:                         0.
% 3.53/1.00  sup_time_generating:                    0.
% 3.53/1.00  sup_time_sim_full:                      0.
% 3.53/1.00  sup_time_sim_immed:                     0.
% 3.53/1.00  
% 3.53/1.00  sup_num_of_clauses:                     139
% 3.53/1.00  sup_num_in_active:                      83
% 3.53/1.00  sup_num_in_passive:                     56
% 3.53/1.00  sup_num_of_loops:                       91
% 3.53/1.00  sup_fw_superposition:                   69
% 3.53/1.00  sup_bw_superposition:                   62
% 3.53/1.00  sup_immediate_simplified:               42
% 3.53/1.00  sup_given_eliminated:                   0
% 3.53/1.00  comparisons_done:                       0
% 3.53/1.00  comparisons_avoided:                    0
% 3.53/1.00  
% 3.53/1.00  ------ Simplifications
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  sim_fw_subset_subsumed:                 7
% 3.53/1.00  sim_bw_subset_subsumed:                 5
% 3.53/1.00  sim_fw_subsumed:                        4
% 3.53/1.00  sim_bw_subsumed:                        2
% 3.53/1.00  sim_fw_subsumption_res:                 0
% 3.53/1.00  sim_bw_subsumption_res:                 0
% 3.53/1.00  sim_tautology_del:                      0
% 3.53/1.00  sim_eq_tautology_del:                   7
% 3.53/1.00  sim_eq_res_simp:                        1
% 3.53/1.00  sim_fw_demodulated:                     7
% 3.53/1.00  sim_bw_demodulated:                     3
% 3.53/1.00  sim_light_normalised:                   25
% 3.53/1.00  sim_joinable_taut:                      0
% 3.53/1.00  sim_joinable_simp:                      0
% 3.53/1.00  sim_ac_normalised:                      0
% 3.53/1.00  sim_smt_subsumption:                    0
% 3.53/1.00  
%------------------------------------------------------------------------------
