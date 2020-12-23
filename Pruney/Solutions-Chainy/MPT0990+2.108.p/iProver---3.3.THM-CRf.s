%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:19 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :  254 (2391 expanded)
%              Number of clauses        :  147 ( 774 expanded)
%              Number of leaves         :   27 ( 530 expanded)
%              Depth                    :   25
%              Number of atoms          :  725 (15705 expanded)
%              Number of equality atoms :  313 (6004 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
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

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f30,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f66,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f67,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f66])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f67,f73,f72])).

fof(f116,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f114,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f117,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f98,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f119,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f113,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f64,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f64])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f92,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f101,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f129,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f101,f110])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f62])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f115,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f58])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f118,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f24,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f124,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f88,f110])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f125,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f90,f110])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f68])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f131,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f91,f110])).

fof(f99,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1707,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5051,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1707,c_1730])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2107,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2787,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_2788,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2965,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2966,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2965])).

cnf(c_5063,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5051,c_50,c_2788,c_2966])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1705,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_5052,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1730])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_1819,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1876,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1876])).

cnf(c_2124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_2252,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2253,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2252])).

cnf(c_5207,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5052,c_48,c_2124,c_2253])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1713,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3888,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1705,c_1713])).

cnf(c_42,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3890,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3888,c_42])).

cnf(c_24,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_650,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_40])).

cnf(c_651,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_653,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_46])).

cnf(c_1695,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_2305,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1695,c_46,c_45,c_651,c_2123,c_2252])).

cnf(c_35,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1708,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2518,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2305,c_1708])).

cnf(c_47,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2092,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2093,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2092])).

cnf(c_2879,plain,
    ( v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2518,c_47,c_48,c_2093,c_2124,c_2253])).

cnf(c_2880,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2879])).

cnf(c_3902,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3890,c_2880])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3095,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3096,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3095])).

cnf(c_4315,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3902,c_47,c_48,c_2124,c_2253,c_3096])).

cnf(c_5053,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4315,c_1730])).

cnf(c_7167,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5053,c_47,c_48,c_2093,c_2124,c_2253])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1721,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7171,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7167,c_1721])).

cnf(c_35380,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5207,c_7171])).

cnf(c_25,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_636,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_40])).

cnf(c_637,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_639,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_46])).

cnf(c_1696,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_2308,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1696,c_46,c_45,c_637,c_2123,c_2252])).

cnf(c_3903,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_3890,c_2308])).

cnf(c_35387,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35380,c_3903])).

cnf(c_35785,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_5063,c_35387])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1709,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7767,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1707,c_1709])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_8095,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7767,c_49])).

cnf(c_8096,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8095])).

cnf(c_8105,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_8096])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_41,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_462,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_33,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_61,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_464,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_61])).

cnf(c_1703,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1811,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2369,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1703,c_46,c_45,c_44,c_43,c_61,c_462,c_1811])).

cnf(c_8108,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8105,c_2369])).

cnf(c_8536,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8108,c_47])).

cnf(c_27,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1714,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3363,plain,
    ( v4_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1707,c_1714])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1728,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1715,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4769,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3890,c_1715])).

cnf(c_5246,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4769,c_47,c_48,c_2124,c_2253])).

cnf(c_5505,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
    | v4_relat_1(X0,sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1728,c_5246])).

cnf(c_10187,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3363,c_5505])).

cnf(c_3364,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1714])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1722,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4997,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3364,c_1722])).

cnf(c_3317,plain,
    ( ~ v4_relat_1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3318,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | v4_relat_1(sK2,X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3317])).

cnf(c_3320,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v4_relat_1(sK2,sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3318])).

cnf(c_7051,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4997,c_48,c_2124,c_2253,c_3320,c_3364])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1725,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5211,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_5207,c_1725])).

cnf(c_7053,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_7051,c_5211])).

cnf(c_7054,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7053,c_3890])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1723,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6545,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5207,c_1723])).

cnf(c_8787,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_5063,c_6545])).

cnf(c_8790,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_8787,c_8536])).

cnf(c_14,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_8791,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_8790,c_14])).

cnf(c_10194,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10187,c_7054,c_8791])).

cnf(c_10316,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10194,c_50,c_2788,c_2966])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1720,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5070,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_5063,c_1720])).

cnf(c_10321,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_10316,c_5070])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1731,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1719,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5479,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_1719])).

cnf(c_10441,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_7167,c_5479])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_664,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_40])).

cnf(c_665,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_667,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_46])).

cnf(c_1694,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_5215,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5207,c_1694])).

cnf(c_10442,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_10441,c_5215])).

cnf(c_10318,plain,
    ( k10_relat_1(sK2,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_10316,c_8791])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1724,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5213,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5207,c_1724])).

cnf(c_5216,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5213,c_3890])).

cnf(c_10335,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_10318,c_5216])).

cnf(c_10443,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_10442,c_10335])).

cnf(c_35794,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_35785,c_8536,c_10321,c_10443])).

cnf(c_37,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f122])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35794,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.73/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.73/1.98  
% 11.73/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.73/1.98  
% 11.73/1.98  ------  iProver source info
% 11.73/1.98  
% 11.73/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.73/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.73/1.98  git: non_committed_changes: false
% 11.73/1.98  git: last_make_outside_of_git: false
% 11.73/1.98  
% 11.73/1.98  ------ 
% 11.73/1.98  
% 11.73/1.98  ------ Input Options
% 11.73/1.98  
% 11.73/1.98  --out_options                           all
% 11.73/1.98  --tptp_safe_out                         true
% 11.73/1.98  --problem_path                          ""
% 11.73/1.98  --include_path                          ""
% 11.73/1.98  --clausifier                            res/vclausify_rel
% 11.73/1.98  --clausifier_options                    ""
% 11.73/1.98  --stdin                                 false
% 11.73/1.98  --stats_out                             all
% 11.73/1.98  
% 11.73/1.98  ------ General Options
% 11.73/1.98  
% 11.73/1.98  --fof                                   false
% 11.73/1.98  --time_out_real                         305.
% 11.73/1.98  --time_out_virtual                      -1.
% 11.73/1.98  --symbol_type_check                     false
% 11.73/1.98  --clausify_out                          false
% 11.73/1.98  --sig_cnt_out                           false
% 11.73/1.98  --trig_cnt_out                          false
% 11.73/1.98  --trig_cnt_out_tolerance                1.
% 11.73/1.98  --trig_cnt_out_sk_spl                   false
% 11.73/1.98  --abstr_cl_out                          false
% 11.73/1.98  
% 11.73/1.98  ------ Global Options
% 11.73/1.98  
% 11.73/1.98  --schedule                              default
% 11.73/1.98  --add_important_lit                     false
% 11.73/1.98  --prop_solver_per_cl                    1000
% 11.73/1.98  --min_unsat_core                        false
% 11.73/1.98  --soft_assumptions                      false
% 11.73/1.98  --soft_lemma_size                       3
% 11.73/1.98  --prop_impl_unit_size                   0
% 11.73/1.98  --prop_impl_unit                        []
% 11.73/1.98  --share_sel_clauses                     true
% 11.73/1.98  --reset_solvers                         false
% 11.73/1.98  --bc_imp_inh                            [conj_cone]
% 11.73/1.98  --conj_cone_tolerance                   3.
% 11.73/1.98  --extra_neg_conj                        none
% 11.73/1.98  --large_theory_mode                     true
% 11.73/1.98  --prolific_symb_bound                   200
% 11.73/1.98  --lt_threshold                          2000
% 11.73/1.98  --clause_weak_htbl                      true
% 11.73/1.98  --gc_record_bc_elim                     false
% 11.73/1.98  
% 11.73/1.98  ------ Preprocessing Options
% 11.73/1.98  
% 11.73/1.98  --preprocessing_flag                    true
% 11.73/1.98  --time_out_prep_mult                    0.1
% 11.73/1.98  --splitting_mode                        input
% 11.73/1.98  --splitting_grd                         true
% 11.73/1.98  --splitting_cvd                         false
% 11.73/1.98  --splitting_cvd_svl                     false
% 11.73/1.98  --splitting_nvd                         32
% 11.73/1.98  --sub_typing                            true
% 11.73/1.98  --prep_gs_sim                           true
% 11.73/1.98  --prep_unflatten                        true
% 11.73/1.98  --prep_res_sim                          true
% 11.73/1.98  --prep_upred                            true
% 11.73/1.98  --prep_sem_filter                       exhaustive
% 11.73/1.98  --prep_sem_filter_out                   false
% 11.73/1.98  --pred_elim                             true
% 11.73/1.98  --res_sim_input                         true
% 11.73/1.98  --eq_ax_congr_red                       true
% 11.73/1.98  --pure_diseq_elim                       true
% 11.73/1.98  --brand_transform                       false
% 11.73/1.98  --non_eq_to_eq                          false
% 11.73/1.98  --prep_def_merge                        true
% 11.73/1.98  --prep_def_merge_prop_impl              false
% 11.73/1.98  --prep_def_merge_mbd                    true
% 11.73/1.98  --prep_def_merge_tr_red                 false
% 11.73/1.98  --prep_def_merge_tr_cl                  false
% 11.73/1.98  --smt_preprocessing                     true
% 11.73/1.98  --smt_ac_axioms                         fast
% 11.73/1.98  --preprocessed_out                      false
% 11.73/1.98  --preprocessed_stats                    false
% 11.73/1.98  
% 11.73/1.98  ------ Abstraction refinement Options
% 11.73/1.98  
% 11.73/1.98  --abstr_ref                             []
% 11.73/1.98  --abstr_ref_prep                        false
% 11.73/1.98  --abstr_ref_until_sat                   false
% 11.73/1.98  --abstr_ref_sig_restrict                funpre
% 11.73/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/1.98  --abstr_ref_under                       []
% 11.73/1.98  
% 11.73/1.98  ------ SAT Options
% 11.73/1.98  
% 11.73/1.98  --sat_mode                              false
% 11.73/1.98  --sat_fm_restart_options                ""
% 11.73/1.98  --sat_gr_def                            false
% 11.73/1.98  --sat_epr_types                         true
% 11.73/1.98  --sat_non_cyclic_types                  false
% 11.73/1.98  --sat_finite_models                     false
% 11.73/1.98  --sat_fm_lemmas                         false
% 11.73/1.98  --sat_fm_prep                           false
% 11.73/1.98  --sat_fm_uc_incr                        true
% 11.73/1.98  --sat_out_model                         small
% 11.73/1.98  --sat_out_clauses                       false
% 11.73/1.98  
% 11.73/1.98  ------ QBF Options
% 11.73/1.98  
% 11.73/1.98  --qbf_mode                              false
% 11.73/1.98  --qbf_elim_univ                         false
% 11.73/1.98  --qbf_dom_inst                          none
% 11.73/1.98  --qbf_dom_pre_inst                      false
% 11.73/1.98  --qbf_sk_in                             false
% 11.73/1.98  --qbf_pred_elim                         true
% 11.73/1.98  --qbf_split                             512
% 11.73/1.98  
% 11.73/1.98  ------ BMC1 Options
% 11.73/1.98  
% 11.73/1.98  --bmc1_incremental                      false
% 11.73/1.98  --bmc1_axioms                           reachable_all
% 11.73/1.98  --bmc1_min_bound                        0
% 11.73/1.98  --bmc1_max_bound                        -1
% 11.73/1.98  --bmc1_max_bound_default                -1
% 11.73/1.98  --bmc1_symbol_reachability              true
% 11.73/1.98  --bmc1_property_lemmas                  false
% 11.73/1.98  --bmc1_k_induction                      false
% 11.73/1.98  --bmc1_non_equiv_states                 false
% 11.73/1.98  --bmc1_deadlock                         false
% 11.73/1.98  --bmc1_ucm                              false
% 11.73/1.98  --bmc1_add_unsat_core                   none
% 11.73/1.98  --bmc1_unsat_core_children              false
% 11.73/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/1.98  --bmc1_out_stat                         full
% 11.73/1.98  --bmc1_ground_init                      false
% 11.73/1.98  --bmc1_pre_inst_next_state              false
% 11.73/1.98  --bmc1_pre_inst_state                   false
% 11.73/1.98  --bmc1_pre_inst_reach_state             false
% 11.73/1.98  --bmc1_out_unsat_core                   false
% 11.73/1.98  --bmc1_aig_witness_out                  false
% 11.73/1.98  --bmc1_verbose                          false
% 11.73/1.98  --bmc1_dump_clauses_tptp                false
% 11.73/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.73/1.98  --bmc1_dump_file                        -
% 11.73/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.73/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.73/1.98  --bmc1_ucm_extend_mode                  1
% 11.73/1.98  --bmc1_ucm_init_mode                    2
% 11.73/1.98  --bmc1_ucm_cone_mode                    none
% 11.73/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.73/1.98  --bmc1_ucm_relax_model                  4
% 11.73/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.73/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/1.98  --bmc1_ucm_layered_model                none
% 11.73/1.98  --bmc1_ucm_max_lemma_size               10
% 11.73/1.98  
% 11.73/1.98  ------ AIG Options
% 11.73/1.98  
% 11.73/1.98  --aig_mode                              false
% 11.73/1.98  
% 11.73/1.98  ------ Instantiation Options
% 11.73/1.98  
% 11.73/1.98  --instantiation_flag                    true
% 11.73/1.98  --inst_sos_flag                         true
% 11.73/1.98  --inst_sos_phase                        true
% 11.73/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/1.98  --inst_lit_sel_side                     num_symb
% 11.73/1.98  --inst_solver_per_active                1400
% 11.73/1.98  --inst_solver_calls_frac                1.
% 11.73/1.98  --inst_passive_queue_type               priority_queues
% 11.73/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/1.98  --inst_passive_queues_freq              [25;2]
% 11.73/1.98  --inst_dismatching                      true
% 11.73/1.98  --inst_eager_unprocessed_to_passive     true
% 11.73/1.98  --inst_prop_sim_given                   true
% 11.73/1.98  --inst_prop_sim_new                     false
% 11.73/1.98  --inst_subs_new                         false
% 11.73/1.98  --inst_eq_res_simp                      false
% 11.73/1.98  --inst_subs_given                       false
% 11.73/1.98  --inst_orphan_elimination               true
% 11.73/1.98  --inst_learning_loop_flag               true
% 11.73/1.98  --inst_learning_start                   3000
% 11.73/1.98  --inst_learning_factor                  2
% 11.73/1.98  --inst_start_prop_sim_after_learn       3
% 11.73/1.98  --inst_sel_renew                        solver
% 11.73/1.98  --inst_lit_activity_flag                true
% 11.73/1.98  --inst_restr_to_given                   false
% 11.73/1.98  --inst_activity_threshold               500
% 11.73/1.98  --inst_out_proof                        true
% 11.73/1.98  
% 11.73/1.98  ------ Resolution Options
% 11.73/1.98  
% 11.73/1.98  --resolution_flag                       true
% 11.73/1.98  --res_lit_sel                           adaptive
% 11.73/1.98  --res_lit_sel_side                      none
% 11.73/1.98  --res_ordering                          kbo
% 11.73/1.98  --res_to_prop_solver                    active
% 11.73/1.98  --res_prop_simpl_new                    false
% 11.73/1.98  --res_prop_simpl_given                  true
% 11.73/1.98  --res_passive_queue_type                priority_queues
% 11.73/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/1.98  --res_passive_queues_freq               [15;5]
% 11.73/1.98  --res_forward_subs                      full
% 11.73/1.98  --res_backward_subs                     full
% 11.73/1.98  --res_forward_subs_resolution           true
% 11.73/1.98  --res_backward_subs_resolution          true
% 11.73/1.98  --res_orphan_elimination                true
% 11.73/1.98  --res_time_limit                        2.
% 11.73/1.98  --res_out_proof                         true
% 11.73/1.98  
% 11.73/1.98  ------ Superposition Options
% 11.73/1.98  
% 11.73/1.98  --superposition_flag                    true
% 11.73/1.98  --sup_passive_queue_type                priority_queues
% 11.73/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.73/1.98  --demod_completeness_check              fast
% 11.73/1.98  --demod_use_ground                      true
% 11.73/1.98  --sup_to_prop_solver                    passive
% 11.73/1.98  --sup_prop_simpl_new                    true
% 11.73/1.98  --sup_prop_simpl_given                  true
% 11.73/1.98  --sup_fun_splitting                     true
% 11.73/1.98  --sup_smt_interval                      50000
% 11.73/1.98  
% 11.73/1.98  ------ Superposition Simplification Setup
% 11.73/1.98  
% 11.73/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/1.98  --sup_immed_triv                        [TrivRules]
% 11.73/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.98  --sup_immed_bw_main                     []
% 11.73/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.98  --sup_input_bw                          []
% 11.73/1.98  
% 11.73/1.98  ------ Combination Options
% 11.73/1.98  
% 11.73/1.98  --comb_res_mult                         3
% 11.73/1.98  --comb_sup_mult                         2
% 11.73/1.98  --comb_inst_mult                        10
% 11.73/1.98  
% 11.73/1.98  ------ Debug Options
% 11.73/1.98  
% 11.73/1.98  --dbg_backtrace                         false
% 11.73/1.98  --dbg_dump_prop_clauses                 false
% 11.73/1.98  --dbg_dump_prop_clauses_file            -
% 11.73/1.98  --dbg_out_stat                          false
% 11.73/1.98  ------ Parsing...
% 11.73/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.73/1.98  
% 11.73/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.73/1.98  
% 11.73/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.73/1.98  
% 11.73/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.73/1.98  ------ Proving...
% 11.73/1.98  ------ Problem Properties 
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  clauses                                 46
% 11.73/1.98  conjectures                             8
% 11.73/1.98  EPR                                     6
% 11.73/1.98  Horn                                    46
% 11.73/1.98  unary                                   14
% 11.73/1.98  binary                                  15
% 11.73/1.98  lits                                    103
% 11.73/1.98  lits eq                                 29
% 11.73/1.98  fd_pure                                 0
% 11.73/1.98  fd_pseudo                               0
% 11.73/1.98  fd_cond                                 0
% 11.73/1.98  fd_pseudo_cond                          1
% 11.73/1.98  AC symbols                              0
% 11.73/1.98  
% 11.73/1.98  ------ Schedule dynamic 5 is on 
% 11.73/1.98  
% 11.73/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  ------ 
% 11.73/1.98  Current options:
% 11.73/1.98  ------ 
% 11.73/1.98  
% 11.73/1.98  ------ Input Options
% 11.73/1.98  
% 11.73/1.98  --out_options                           all
% 11.73/1.98  --tptp_safe_out                         true
% 11.73/1.98  --problem_path                          ""
% 11.73/1.98  --include_path                          ""
% 11.73/1.98  --clausifier                            res/vclausify_rel
% 11.73/1.98  --clausifier_options                    ""
% 11.73/1.98  --stdin                                 false
% 11.73/1.98  --stats_out                             all
% 11.73/1.98  
% 11.73/1.98  ------ General Options
% 11.73/1.98  
% 11.73/1.98  --fof                                   false
% 11.73/1.98  --time_out_real                         305.
% 11.73/1.98  --time_out_virtual                      -1.
% 11.73/1.98  --symbol_type_check                     false
% 11.73/1.98  --clausify_out                          false
% 11.73/1.98  --sig_cnt_out                           false
% 11.73/1.98  --trig_cnt_out                          false
% 11.73/1.98  --trig_cnt_out_tolerance                1.
% 11.73/1.98  --trig_cnt_out_sk_spl                   false
% 11.73/1.98  --abstr_cl_out                          false
% 11.73/1.98  
% 11.73/1.98  ------ Global Options
% 11.73/1.98  
% 11.73/1.98  --schedule                              default
% 11.73/1.98  --add_important_lit                     false
% 11.73/1.98  --prop_solver_per_cl                    1000
% 11.73/1.98  --min_unsat_core                        false
% 11.73/1.98  --soft_assumptions                      false
% 11.73/1.98  --soft_lemma_size                       3
% 11.73/1.98  --prop_impl_unit_size                   0
% 11.73/1.98  --prop_impl_unit                        []
% 11.73/1.98  --share_sel_clauses                     true
% 11.73/1.98  --reset_solvers                         false
% 11.73/1.98  --bc_imp_inh                            [conj_cone]
% 11.73/1.98  --conj_cone_tolerance                   3.
% 11.73/1.98  --extra_neg_conj                        none
% 11.73/1.98  --large_theory_mode                     true
% 11.73/1.98  --prolific_symb_bound                   200
% 11.73/1.98  --lt_threshold                          2000
% 11.73/1.98  --clause_weak_htbl                      true
% 11.73/1.98  --gc_record_bc_elim                     false
% 11.73/1.98  
% 11.73/1.98  ------ Preprocessing Options
% 11.73/1.98  
% 11.73/1.98  --preprocessing_flag                    true
% 11.73/1.98  --time_out_prep_mult                    0.1
% 11.73/1.98  --splitting_mode                        input
% 11.73/1.98  --splitting_grd                         true
% 11.73/1.98  --splitting_cvd                         false
% 11.73/1.98  --splitting_cvd_svl                     false
% 11.73/1.98  --splitting_nvd                         32
% 11.73/1.98  --sub_typing                            true
% 11.73/1.98  --prep_gs_sim                           true
% 11.73/1.98  --prep_unflatten                        true
% 11.73/1.98  --prep_res_sim                          true
% 11.73/1.98  --prep_upred                            true
% 11.73/1.98  --prep_sem_filter                       exhaustive
% 11.73/1.98  --prep_sem_filter_out                   false
% 11.73/1.98  --pred_elim                             true
% 11.73/1.98  --res_sim_input                         true
% 11.73/1.98  --eq_ax_congr_red                       true
% 11.73/1.98  --pure_diseq_elim                       true
% 11.73/1.98  --brand_transform                       false
% 11.73/1.98  --non_eq_to_eq                          false
% 11.73/1.98  --prep_def_merge                        true
% 11.73/1.98  --prep_def_merge_prop_impl              false
% 11.73/1.98  --prep_def_merge_mbd                    true
% 11.73/1.98  --prep_def_merge_tr_red                 false
% 11.73/1.98  --prep_def_merge_tr_cl                  false
% 11.73/1.98  --smt_preprocessing                     true
% 11.73/1.98  --smt_ac_axioms                         fast
% 11.73/1.98  --preprocessed_out                      false
% 11.73/1.98  --preprocessed_stats                    false
% 11.73/1.98  
% 11.73/1.98  ------ Abstraction refinement Options
% 11.73/1.98  
% 11.73/1.98  --abstr_ref                             []
% 11.73/1.98  --abstr_ref_prep                        false
% 11.73/1.98  --abstr_ref_until_sat                   false
% 11.73/1.98  --abstr_ref_sig_restrict                funpre
% 11.73/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/1.98  --abstr_ref_under                       []
% 11.73/1.98  
% 11.73/1.98  ------ SAT Options
% 11.73/1.98  
% 11.73/1.98  --sat_mode                              false
% 11.73/1.98  --sat_fm_restart_options                ""
% 11.73/1.98  --sat_gr_def                            false
% 11.73/1.98  --sat_epr_types                         true
% 11.73/1.98  --sat_non_cyclic_types                  false
% 11.73/1.98  --sat_finite_models                     false
% 11.73/1.98  --sat_fm_lemmas                         false
% 11.73/1.98  --sat_fm_prep                           false
% 11.73/1.98  --sat_fm_uc_incr                        true
% 11.73/1.98  --sat_out_model                         small
% 11.73/1.98  --sat_out_clauses                       false
% 11.73/1.98  
% 11.73/1.98  ------ QBF Options
% 11.73/1.98  
% 11.73/1.98  --qbf_mode                              false
% 11.73/1.98  --qbf_elim_univ                         false
% 11.73/1.98  --qbf_dom_inst                          none
% 11.73/1.98  --qbf_dom_pre_inst                      false
% 11.73/1.98  --qbf_sk_in                             false
% 11.73/1.98  --qbf_pred_elim                         true
% 11.73/1.98  --qbf_split                             512
% 11.73/1.98  
% 11.73/1.98  ------ BMC1 Options
% 11.73/1.98  
% 11.73/1.98  --bmc1_incremental                      false
% 11.73/1.98  --bmc1_axioms                           reachable_all
% 11.73/1.98  --bmc1_min_bound                        0
% 11.73/1.98  --bmc1_max_bound                        -1
% 11.73/1.98  --bmc1_max_bound_default                -1
% 11.73/1.98  --bmc1_symbol_reachability              true
% 11.73/1.98  --bmc1_property_lemmas                  false
% 11.73/1.98  --bmc1_k_induction                      false
% 11.73/1.98  --bmc1_non_equiv_states                 false
% 11.73/1.98  --bmc1_deadlock                         false
% 11.73/1.98  --bmc1_ucm                              false
% 11.73/1.98  --bmc1_add_unsat_core                   none
% 11.73/1.98  --bmc1_unsat_core_children              false
% 11.73/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/1.98  --bmc1_out_stat                         full
% 11.73/1.98  --bmc1_ground_init                      false
% 11.73/1.98  --bmc1_pre_inst_next_state              false
% 11.73/1.98  --bmc1_pre_inst_state                   false
% 11.73/1.98  --bmc1_pre_inst_reach_state             false
% 11.73/1.98  --bmc1_out_unsat_core                   false
% 11.73/1.98  --bmc1_aig_witness_out                  false
% 11.73/1.98  --bmc1_verbose                          false
% 11.73/1.98  --bmc1_dump_clauses_tptp                false
% 11.73/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.73/1.98  --bmc1_dump_file                        -
% 11.73/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.73/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.73/1.98  --bmc1_ucm_extend_mode                  1
% 11.73/1.98  --bmc1_ucm_init_mode                    2
% 11.73/1.98  --bmc1_ucm_cone_mode                    none
% 11.73/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.73/1.98  --bmc1_ucm_relax_model                  4
% 11.73/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.73/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/1.98  --bmc1_ucm_layered_model                none
% 11.73/1.98  --bmc1_ucm_max_lemma_size               10
% 11.73/1.98  
% 11.73/1.98  ------ AIG Options
% 11.73/1.98  
% 11.73/1.98  --aig_mode                              false
% 11.73/1.98  
% 11.73/1.98  ------ Instantiation Options
% 11.73/1.98  
% 11.73/1.98  --instantiation_flag                    true
% 11.73/1.98  --inst_sos_flag                         true
% 11.73/1.98  --inst_sos_phase                        true
% 11.73/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/1.98  --inst_lit_sel_side                     none
% 11.73/1.98  --inst_solver_per_active                1400
% 11.73/1.98  --inst_solver_calls_frac                1.
% 11.73/1.98  --inst_passive_queue_type               priority_queues
% 11.73/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/1.98  --inst_passive_queues_freq              [25;2]
% 11.73/1.98  --inst_dismatching                      true
% 11.73/1.98  --inst_eager_unprocessed_to_passive     true
% 11.73/1.98  --inst_prop_sim_given                   true
% 11.73/1.98  --inst_prop_sim_new                     false
% 11.73/1.98  --inst_subs_new                         false
% 11.73/1.98  --inst_eq_res_simp                      false
% 11.73/1.98  --inst_subs_given                       false
% 11.73/1.98  --inst_orphan_elimination               true
% 11.73/1.98  --inst_learning_loop_flag               true
% 11.73/1.98  --inst_learning_start                   3000
% 11.73/1.98  --inst_learning_factor                  2
% 11.73/1.98  --inst_start_prop_sim_after_learn       3
% 11.73/1.98  --inst_sel_renew                        solver
% 11.73/1.98  --inst_lit_activity_flag                true
% 11.73/1.98  --inst_restr_to_given                   false
% 11.73/1.98  --inst_activity_threshold               500
% 11.73/1.98  --inst_out_proof                        true
% 11.73/1.98  
% 11.73/1.98  ------ Resolution Options
% 11.73/1.98  
% 11.73/1.98  --resolution_flag                       false
% 11.73/1.98  --res_lit_sel                           adaptive
% 11.73/1.98  --res_lit_sel_side                      none
% 11.73/1.98  --res_ordering                          kbo
% 11.73/1.98  --res_to_prop_solver                    active
% 11.73/1.98  --res_prop_simpl_new                    false
% 11.73/1.98  --res_prop_simpl_given                  true
% 11.73/1.98  --res_passive_queue_type                priority_queues
% 11.73/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/1.98  --res_passive_queues_freq               [15;5]
% 11.73/1.98  --res_forward_subs                      full
% 11.73/1.98  --res_backward_subs                     full
% 11.73/1.98  --res_forward_subs_resolution           true
% 11.73/1.98  --res_backward_subs_resolution          true
% 11.73/1.98  --res_orphan_elimination                true
% 11.73/1.98  --res_time_limit                        2.
% 11.73/1.98  --res_out_proof                         true
% 11.73/1.98  
% 11.73/1.98  ------ Superposition Options
% 11.73/1.98  
% 11.73/1.98  --superposition_flag                    true
% 11.73/1.98  --sup_passive_queue_type                priority_queues
% 11.73/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.73/1.98  --demod_completeness_check              fast
% 11.73/1.98  --demod_use_ground                      true
% 11.73/1.98  --sup_to_prop_solver                    passive
% 11.73/1.98  --sup_prop_simpl_new                    true
% 11.73/1.98  --sup_prop_simpl_given                  true
% 11.73/1.98  --sup_fun_splitting                     true
% 11.73/1.98  --sup_smt_interval                      50000
% 11.73/1.98  
% 11.73/1.98  ------ Superposition Simplification Setup
% 11.73/1.98  
% 11.73/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/1.98  --sup_immed_triv                        [TrivRules]
% 11.73/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.98  --sup_immed_bw_main                     []
% 11.73/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.98  --sup_input_bw                          []
% 11.73/1.98  
% 11.73/1.98  ------ Combination Options
% 11.73/1.98  
% 11.73/1.98  --comb_res_mult                         3
% 11.73/1.98  --comb_sup_mult                         2
% 11.73/1.98  --comb_inst_mult                        10
% 11.73/1.98  
% 11.73/1.98  ------ Debug Options
% 11.73/1.98  
% 11.73/1.98  --dbg_backtrace                         false
% 11.73/1.98  --dbg_dump_prop_clauses                 false
% 11.73/1.98  --dbg_dump_prop_clauses_file            -
% 11.73/1.98  --dbg_out_stat                          false
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  ------ Proving...
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  % SZS status Theorem for theBenchmark.p
% 11.73/1.98  
% 11.73/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.73/1.98  
% 11.73/1.98  fof(f28,conjecture,(
% 11.73/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f29,negated_conjecture,(
% 11.73/1.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.73/1.98    inference(negated_conjecture,[],[f28])).
% 11.73/1.98  
% 11.73/1.98  fof(f30,plain,(
% 11.73/1.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.73/1.98    inference(pure_predicate_removal,[],[f29])).
% 11.73/1.98  
% 11.73/1.98  fof(f66,plain,(
% 11.73/1.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 11.73/1.98    inference(ennf_transformation,[],[f30])).
% 11.73/1.98  
% 11.73/1.98  fof(f67,plain,(
% 11.73/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 11.73/1.98    inference(flattening,[],[f66])).
% 11.73/1.98  
% 11.73/1.98  fof(f73,plain,(
% 11.73/1.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 11.73/1.98    introduced(choice_axiom,[])).
% 11.73/1.98  
% 11.73/1.98  fof(f72,plain,(
% 11.73/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 11.73/1.98    introduced(choice_axiom,[])).
% 11.73/1.98  
% 11.73/1.98  fof(f74,plain,(
% 11.73/1.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 11.73/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f67,f73,f72])).
% 11.73/1.98  
% 11.73/1.98  fof(f116,plain,(
% 11.73/1.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  fof(f2,axiom,(
% 11.73/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f34,plain,(
% 11.73/1.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(ennf_transformation,[],[f2])).
% 11.73/1.98  
% 11.73/1.98  fof(f78,plain,(
% 11.73/1.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f34])).
% 11.73/1.98  
% 11.73/1.98  fof(f4,axiom,(
% 11.73/1.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f81,plain,(
% 11.73/1.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.73/1.98    inference(cnf_transformation,[],[f4])).
% 11.73/1.98  
% 11.73/1.98  fof(f114,plain,(
% 11.73/1.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  fof(f21,axiom,(
% 11.73/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f57,plain,(
% 11.73/1.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/1.98    inference(ennf_transformation,[],[f21])).
% 11.73/1.98  
% 11.73/1.98  fof(f103,plain,(
% 11.73/1.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/1.98    inference(cnf_transformation,[],[f57])).
% 11.73/1.98  
% 11.73/1.98  fof(f117,plain,(
% 11.73/1.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  fof(f18,axiom,(
% 11.73/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f52,plain,(
% 11.73/1.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.73/1.98    inference(ennf_transformation,[],[f18])).
% 11.73/1.98  
% 11.73/1.98  fof(f53,plain,(
% 11.73/1.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(flattening,[],[f52])).
% 11.73/1.98  
% 11.73/1.98  fof(f98,plain,(
% 11.73/1.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f53])).
% 11.73/1.98  
% 11.73/1.98  fof(f119,plain,(
% 11.73/1.98    v2_funct_1(sK2)),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  fof(f113,plain,(
% 11.73/1.98    v1_funct_1(sK2)),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  fof(f27,axiom,(
% 11.73/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f31,plain,(
% 11.73/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 11.73/1.98    inference(pure_predicate_removal,[],[f27])).
% 11.73/1.98  
% 11.73/1.98  fof(f64,plain,(
% 11.73/1.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.73/1.98    inference(ennf_transformation,[],[f31])).
% 11.73/1.98  
% 11.73/1.98  fof(f65,plain,(
% 11.73/1.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(flattening,[],[f64])).
% 11.73/1.98  
% 11.73/1.98  fof(f112,plain,(
% 11.73/1.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f65])).
% 11.73/1.98  
% 11.73/1.98  fof(f14,axiom,(
% 11.73/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f46,plain,(
% 11.73/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.73/1.98    inference(ennf_transformation,[],[f14])).
% 11.73/1.98  
% 11.73/1.98  fof(f47,plain,(
% 11.73/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(flattening,[],[f46])).
% 11.73/1.98  
% 11.73/1.98  fof(f92,plain,(
% 11.73/1.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f47])).
% 11.73/1.98  
% 11.73/1.98  fof(f93,plain,(
% 11.73/1.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f47])).
% 11.73/1.98  
% 11.73/1.98  fof(f10,axiom,(
% 11.73/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f42,plain,(
% 11.73/1.98    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(ennf_transformation,[],[f10])).
% 11.73/1.98  
% 11.73/1.98  fof(f87,plain,(
% 11.73/1.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f42])).
% 11.73/1.98  
% 11.73/1.98  fof(f19,axiom,(
% 11.73/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f54,plain,(
% 11.73/1.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.73/1.98    inference(ennf_transformation,[],[f19])).
% 11.73/1.98  
% 11.73/1.98  fof(f55,plain,(
% 11.73/1.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(flattening,[],[f54])).
% 11.73/1.98  
% 11.73/1.98  fof(f101,plain,(
% 11.73/1.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f55])).
% 11.73/1.98  
% 11.73/1.98  fof(f26,axiom,(
% 11.73/1.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f110,plain,(
% 11.73/1.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f26])).
% 11.73/1.98  
% 11.73/1.98  fof(f129,plain,(
% 11.73/1.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(definition_unfolding,[],[f101,f110])).
% 11.73/1.98  
% 11.73/1.98  fof(f25,axiom,(
% 11.73/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f62,plain,(
% 11.73/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.73/1.98    inference(ennf_transformation,[],[f25])).
% 11.73/1.98  
% 11.73/1.98  fof(f63,plain,(
% 11.73/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.73/1.98    inference(flattening,[],[f62])).
% 11.73/1.98  
% 11.73/1.98  fof(f109,plain,(
% 11.73/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f63])).
% 11.73/1.98  
% 11.73/1.98  fof(f115,plain,(
% 11.73/1.98    v1_funct_1(sK3)),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  fof(f22,axiom,(
% 11.73/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f58,plain,(
% 11.73/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.73/1.98    inference(ennf_transformation,[],[f22])).
% 11.73/1.98  
% 11.73/1.98  fof(f59,plain,(
% 11.73/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/1.98    inference(flattening,[],[f58])).
% 11.73/1.98  
% 11.73/1.98  fof(f71,plain,(
% 11.73/1.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/1.98    inference(nnf_transformation,[],[f59])).
% 11.73/1.98  
% 11.73/1.98  fof(f104,plain,(
% 11.73/1.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/1.98    inference(cnf_transformation,[],[f71])).
% 11.73/1.98  
% 11.73/1.98  fof(f118,plain,(
% 11.73/1.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  fof(f24,axiom,(
% 11.73/1.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f32,plain,(
% 11.73/1.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.73/1.98    inference(pure_predicate_removal,[],[f24])).
% 11.73/1.98  
% 11.73/1.98  fof(f108,plain,(
% 11.73/1.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.73/1.98    inference(cnf_transformation,[],[f32])).
% 11.73/1.98  
% 11.73/1.98  fof(f23,axiom,(
% 11.73/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f60,plain,(
% 11.73/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.73/1.98    inference(ennf_transformation,[],[f23])).
% 11.73/1.98  
% 11.73/1.98  fof(f61,plain,(
% 11.73/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.73/1.98    inference(flattening,[],[f60])).
% 11.73/1.98  
% 11.73/1.98  fof(f107,plain,(
% 11.73/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f61])).
% 11.73/1.98  
% 11.73/1.98  fof(f20,axiom,(
% 11.73/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f33,plain,(
% 11.73/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.73/1.98    inference(pure_predicate_removal,[],[f20])).
% 11.73/1.98  
% 11.73/1.98  fof(f56,plain,(
% 11.73/1.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/1.98    inference(ennf_transformation,[],[f33])).
% 11.73/1.98  
% 11.73/1.98  fof(f102,plain,(
% 11.73/1.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/1.98    inference(cnf_transformation,[],[f56])).
% 11.73/1.98  
% 11.73/1.98  fof(f3,axiom,(
% 11.73/1.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f35,plain,(
% 11.73/1.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.73/1.98    inference(ennf_transformation,[],[f3])).
% 11.73/1.98  
% 11.73/1.98  fof(f70,plain,(
% 11.73/1.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.73/1.98    inference(nnf_transformation,[],[f35])).
% 11.73/1.98  
% 11.73/1.98  fof(f79,plain,(
% 11.73/1.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f70])).
% 11.73/1.98  
% 11.73/1.98  fof(f16,axiom,(
% 11.73/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f48,plain,(
% 11.73/1.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.73/1.98    inference(ennf_transformation,[],[f16])).
% 11.73/1.98  
% 11.73/1.98  fof(f49,plain,(
% 11.73/1.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.73/1.98    inference(flattening,[],[f48])).
% 11.73/1.98  
% 11.73/1.98  fof(f96,plain,(
% 11.73/1.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f49])).
% 11.73/1.98  
% 11.73/1.98  fof(f9,axiom,(
% 11.73/1.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f40,plain,(
% 11.73/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.73/1.98    inference(ennf_transformation,[],[f9])).
% 11.73/1.98  
% 11.73/1.98  fof(f41,plain,(
% 11.73/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.73/1.98    inference(flattening,[],[f40])).
% 11.73/1.98  
% 11.73/1.98  fof(f86,plain,(
% 11.73/1.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f41])).
% 11.73/1.98  
% 11.73/1.98  fof(f6,axiom,(
% 11.73/1.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f37,plain,(
% 11.73/1.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.73/1.98    inference(ennf_transformation,[],[f6])).
% 11.73/1.98  
% 11.73/1.98  fof(f83,plain,(
% 11.73/1.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f37])).
% 11.73/1.98  
% 11.73/1.98  fof(f8,axiom,(
% 11.73/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f39,plain,(
% 11.73/1.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(ennf_transformation,[],[f8])).
% 11.73/1.98  
% 11.73/1.98  fof(f85,plain,(
% 11.73/1.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f39])).
% 11.73/1.98  
% 11.73/1.98  fof(f11,axiom,(
% 11.73/1.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f88,plain,(
% 11.73/1.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.73/1.98    inference(cnf_transformation,[],[f11])).
% 11.73/1.98  
% 11.73/1.98  fof(f124,plain,(
% 11.73/1.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.73/1.98    inference(definition_unfolding,[],[f88,f110])).
% 11.73/1.98  
% 11.73/1.98  fof(f12,axiom,(
% 11.73/1.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f43,plain,(
% 11.73/1.98    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 11.73/1.98    inference(ennf_transformation,[],[f12])).
% 11.73/1.98  
% 11.73/1.98  fof(f90,plain,(
% 11.73/1.98    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f43])).
% 11.73/1.98  
% 11.73/1.98  fof(f125,plain,(
% 11.73/1.98    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(definition_unfolding,[],[f90,f110])).
% 11.73/1.98  
% 11.73/1.98  fof(f1,axiom,(
% 11.73/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f68,plain,(
% 11.73/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.73/1.98    inference(nnf_transformation,[],[f1])).
% 11.73/1.98  
% 11.73/1.98  fof(f69,plain,(
% 11.73/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.73/1.98    inference(flattening,[],[f68])).
% 11.73/1.98  
% 11.73/1.98  fof(f76,plain,(
% 11.73/1.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.73/1.98    inference(cnf_transformation,[],[f69])).
% 11.73/1.98  
% 11.73/1.98  fof(f131,plain,(
% 11.73/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.73/1.98    inference(equality_resolution,[],[f76])).
% 11.73/1.98  
% 11.73/1.98  fof(f13,axiom,(
% 11.73/1.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f44,plain,(
% 11.73/1.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.73/1.98    inference(ennf_transformation,[],[f13])).
% 11.73/1.98  
% 11.73/1.98  fof(f45,plain,(
% 11.73/1.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.73/1.98    inference(flattening,[],[f44])).
% 11.73/1.98  
% 11.73/1.98  fof(f91,plain,(
% 11.73/1.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f45])).
% 11.73/1.98  
% 11.73/1.98  fof(f126,plain,(
% 11.73/1.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.73/1.98    inference(definition_unfolding,[],[f91,f110])).
% 11.73/1.98  
% 11.73/1.98  fof(f99,plain,(
% 11.73/1.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f53])).
% 11.73/1.98  
% 11.73/1.98  fof(f7,axiom,(
% 11.73/1.98    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 11.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.98  
% 11.73/1.98  fof(f38,plain,(
% 11.73/1.98    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 11.73/1.98    inference(ennf_transformation,[],[f7])).
% 11.73/1.98  
% 11.73/1.98  fof(f84,plain,(
% 11.73/1.98    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 11.73/1.98    inference(cnf_transformation,[],[f38])).
% 11.73/1.98  
% 11.73/1.98  fof(f122,plain,(
% 11.73/1.98    k2_funct_1(sK2) != sK3),
% 11.73/1.98    inference(cnf_transformation,[],[f74])).
% 11.73/1.98  
% 11.73/1.98  cnf(c_43,negated_conjecture,
% 11.73/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.73/1.98      inference(cnf_transformation,[],[f116]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1707,plain,
% 11.73/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3,plain,
% 11.73/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.73/1.98      | ~ v1_relat_1(X1)
% 11.73/1.98      | v1_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1730,plain,
% 11.73/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.73/1.98      | v1_relat_1(X1) != iProver_top
% 11.73/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5051,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 11.73/1.98      | v1_relat_1(sK3) = iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1707,c_1730]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_50,plain,
% 11.73/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2107,plain,
% 11.73/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/1.98      | v1_relat_1(X0)
% 11.73/1.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2787,plain,
% 11.73/1.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.73/1.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 11.73/1.98      | v1_relat_1(sK3) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_2107]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2788,plain,
% 11.73/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.73/1.98      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 11.73/1.98      | v1_relat_1(sK3) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_6,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.73/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2965,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_6]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2966,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_2965]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5063,plain,
% 11.73/1.98      ( v1_relat_1(sK3) = iProver_top ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_5051,c_50,c_2788,c_2966]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_45,negated_conjecture,
% 11.73/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.73/1.98      inference(cnf_transformation,[],[f114]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1705,plain,
% 11.73/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5052,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.73/1.98      | v1_relat_1(sK2) = iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1705,c_1730]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_48,plain,
% 11.73/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1819,plain,
% 11.73/1.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | v1_relat_1(sK2) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1876,plain,
% 11.73/1.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.73/1.98      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 11.73/1.98      | v1_relat_1(sK2) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_1819]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2123,plain,
% 11.73/1.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.73/1.98      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 11.73/1.98      | v1_relat_1(sK2) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_1876]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2124,plain,
% 11.73/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.73/1.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.73/1.98      | v1_relat_1(sK2) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2252,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_6]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2253,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_2252]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5207,plain,
% 11.73/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_5052,c_48,c_2124,c_2253]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_28,plain,
% 11.73/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/1.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f103]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1713,plain,
% 11.73/1.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.73/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3888,plain,
% 11.73/1.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1705,c_1713]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_42,negated_conjecture,
% 11.73/1.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.73/1.98      inference(cnf_transformation,[],[f117]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3890,plain,
% 11.73/1.98      ( k2_relat_1(sK2) = sK1 ),
% 11.73/1.98      inference(light_normalisation,[status(thm)],[c_3888,c_42]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_24,plain,
% 11.73/1.98      ( ~ v2_funct_1(X0)
% 11.73/1.98      | ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f98]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_40,negated_conjecture,
% 11.73/1.98      ( v2_funct_1(sK2) ),
% 11.73/1.98      inference(cnf_transformation,[],[f119]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_650,plain,
% 11.73/1.98      ( ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 11.73/1.98      | sK2 != X0 ),
% 11.73/1.98      inference(resolution_lifted,[status(thm)],[c_24,c_40]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_651,plain,
% 11.73/1.98      ( ~ v1_funct_1(sK2)
% 11.73/1.98      | ~ v1_relat_1(sK2)
% 11.73/1.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 11.73/1.98      inference(unflattening,[status(thm)],[c_650]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_46,negated_conjecture,
% 11.73/1.98      ( v1_funct_1(sK2) ),
% 11.73/1.98      inference(cnf_transformation,[],[f113]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_653,plain,
% 11.73/1.98      ( ~ v1_relat_1(sK2)
% 11.73/1.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_651,c_46]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1695,plain,
% 11.73/1.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2305,plain,
% 11.73/1.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_1695,c_46,c_45,c_651,c_2123,c_2252]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_35,plain,
% 11.73/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.73/1.98      | ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f112]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1708,plain,
% 11.73/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 11.73/1.98      | v1_funct_1(X0) != iProver_top
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2518,plain,
% 11.73/1.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 11.73/1.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.73/1.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_2305,c_1708]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_47,plain,
% 11.73/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_18,plain,
% 11.73/1.98      ( ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | v1_relat_1(k2_funct_1(X0)) ),
% 11.73/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2092,plain,
% 11.73/1.98      ( ~ v1_funct_1(sK2)
% 11.73/1.98      | v1_relat_1(k2_funct_1(sK2))
% 11.73/1.98      | ~ v1_relat_1(sK2) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_18]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2093,plain,
% 11.73/1.98      ( v1_funct_1(sK2) != iProver_top
% 11.73/1.98      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_2092]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2879,plain,
% 11.73/1.98      ( v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.73/1.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_2518,c_47,c_48,c_2093,c_2124,c_2253]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2880,plain,
% 11.73/1.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 11.73/1.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.73/1.98      inference(renaming,[status(thm)],[c_2879]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3902,plain,
% 11.73/1.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 11.73/1.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.73/1.98      inference(demodulation,[status(thm)],[c_3890,c_2880]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_17,plain,
% 11.73/1.98      ( ~ v1_funct_1(X0)
% 11.73/1.98      | v1_funct_1(k2_funct_1(X0))
% 11.73/1.98      | ~ v1_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3095,plain,
% 11.73/1.98      ( v1_funct_1(k2_funct_1(sK2))
% 11.73/1.98      | ~ v1_funct_1(sK2)
% 11.73/1.98      | ~ v1_relat_1(sK2) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3096,plain,
% 11.73/1.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.73/1.98      | v1_funct_1(sK2) != iProver_top
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_3095]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_4315,plain,
% 11.73/1.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_3902,c_47,c_48,c_2124,c_2253,c_3096]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5053,plain,
% 11.73/1.98      ( v1_relat_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) != iProver_top
% 11.73/1.98      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_4315,c_1730]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_7167,plain,
% 11.73/1.98      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_5053,c_47,c_48,c_2093,c_2124,c_2253]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_12,plain,
% 11.73/1.98      ( ~ v1_relat_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X1)
% 11.73/1.98      | ~ v1_relat_1(X2)
% 11.73/1.98      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 11.73/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1721,plain,
% 11.73/1.98      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 11.73/1.98      | v1_relat_1(X0) != iProver_top
% 11.73/1.98      | v1_relat_1(X1) != iProver_top
% 11.73/1.98      | v1_relat_1(X2) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_7171,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
% 11.73/1.98      | v1_relat_1(X0) != iProver_top
% 11.73/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_7167,c_1721]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_35380,plain,
% 11.73/1.98      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5207,c_7171]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_25,plain,
% 11.73/1.98      ( ~ v2_funct_1(X0)
% 11.73/1.98      | ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 11.73/1.98      inference(cnf_transformation,[],[f129]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_636,plain,
% 11.73/1.98      ( ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 11.73/1.98      | sK2 != X0 ),
% 11.73/1.98      inference(resolution_lifted,[status(thm)],[c_25,c_40]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_637,plain,
% 11.73/1.98      ( ~ v1_funct_1(sK2)
% 11.73/1.98      | ~ v1_relat_1(sK2)
% 11.73/1.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 11.73/1.98      inference(unflattening,[status(thm)],[c_636]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_639,plain,
% 11.73/1.98      ( ~ v1_relat_1(sK2)
% 11.73/1.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_637,c_46]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1696,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2308,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_1696,c_46,c_45,c_637,c_2123,c_2252]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3903,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.73/1.98      inference(demodulation,[status(thm)],[c_3890,c_2308]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_35387,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(light_normalisation,[status(thm)],[c_35380,c_3903]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_35785,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5063,c_35387]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_34,plain,
% 11.73/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.73/1.98      | ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_funct_1(X3)
% 11.73/1.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f109]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1709,plain,
% 11.73/1.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.73/1.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.73/1.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.73/1.98      | v1_funct_1(X5) != iProver_top
% 11.73/1.98      | v1_funct_1(X4) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_7767,plain,
% 11.73/1.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.73/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.73/1.98      | v1_funct_1(X2) != iProver_top
% 11.73/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1707,c_1709]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_44,negated_conjecture,
% 11.73/1.98      ( v1_funct_1(sK3) ),
% 11.73/1.98      inference(cnf_transformation,[],[f115]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_49,plain,
% 11.73/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8095,plain,
% 11.73/1.98      ( v1_funct_1(X2) != iProver_top
% 11.73/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.73/1.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_7767,c_49]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8096,plain,
% 11.73/1.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.73/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.73/1.98      | v1_funct_1(X2) != iProver_top ),
% 11.73/1.98      inference(renaming,[status(thm)],[c_8095]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8105,plain,
% 11.73/1.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.73/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1705,c_8096]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_30,plain,
% 11.73/1.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.73/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.73/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.73/1.98      | X3 = X2 ),
% 11.73/1.98      inference(cnf_transformation,[],[f104]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_41,negated_conjecture,
% 11.73/1.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.73/1.98      inference(cnf_transformation,[],[f118]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_461,plain,
% 11.73/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/1.98      | X3 = X0
% 11.73/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.73/1.98      | k6_partfun1(sK0) != X3
% 11.73/1.98      | sK0 != X2
% 11.73/1.98      | sK0 != X1 ),
% 11.73/1.98      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_462,plain,
% 11.73/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.73/1.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.73/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.73/1.98      inference(unflattening,[status(thm)],[c_461]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_33,plain,
% 11.73/1.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.73/1.98      inference(cnf_transformation,[],[f108]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_61,plain,
% 11.73/1.98      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_33]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_464,plain,
% 11.73/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.73/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_462,c_61]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1703,plain,
% 11.73/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.73/1.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_31,plain,
% 11.73/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.73/1.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.73/1.98      | ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_funct_1(X3) ),
% 11.73/1.98      inference(cnf_transformation,[],[f107]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1811,plain,
% 11.73/1.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.73/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.73/1.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.73/1.98      | ~ v1_funct_1(sK3)
% 11.73/1.98      | ~ v1_funct_1(sK2) ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_31]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_2369,plain,
% 11.73/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_1703,c_46,c_45,c_44,c_43,c_61,c_462,c_1811]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8108,plain,
% 11.73/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.73/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.73/1.98      inference(light_normalisation,[status(thm)],[c_8105,c_2369]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8536,plain,
% 11.73/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_8108,c_47]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_27,plain,
% 11.73/1.98      ( v4_relat_1(X0,X1)
% 11.73/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.73/1.98      inference(cnf_transformation,[],[f102]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1714,plain,
% 11.73/1.98      ( v4_relat_1(X0,X1) = iProver_top
% 11.73/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3363,plain,
% 11.73/1.98      ( v4_relat_1(sK3,sK1) = iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1707,c_1714]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5,plain,
% 11.73/1.98      ( ~ v4_relat_1(X0,X1)
% 11.73/1.98      | r1_tarski(k1_relat_1(X0),X1)
% 11.73/1.98      | ~ v1_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1728,plain,
% 11.73/1.98      ( v4_relat_1(X0,X1) != iProver_top
% 11.73/1.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_21,plain,
% 11.73/1.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 11.73/1.98      | ~ v1_funct_1(X1)
% 11.73/1.98      | ~ v1_relat_1(X1)
% 11.73/1.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 11.73/1.98      inference(cnf_transformation,[],[f96]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1715,plain,
% 11.73/1.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 11.73/1.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 11.73/1.98      | v1_funct_1(X0) != iProver_top
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_4769,plain,
% 11.73/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 11.73/1.98      | r1_tarski(X0,sK1) != iProver_top
% 11.73/1.98      | v1_funct_1(sK2) != iProver_top
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_3890,c_1715]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5246,plain,
% 11.73/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 11.73/1.98      | r1_tarski(X0,sK1) != iProver_top ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_4769,c_47,c_48,c_2124,c_2253]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5505,plain,
% 11.73/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
% 11.73/1.98      | v4_relat_1(X0,sK1) != iProver_top
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1728,c_5246]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10187,plain,
% 11.73/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 11.73/1.98      | v1_relat_1(sK3) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_3363,c_5505]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3364,plain,
% 11.73/1.98      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1705,c_1714]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_11,plain,
% 11.73/1.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.73/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1722,plain,
% 11.73/1.98      ( k7_relat_1(X0,X1) = X0
% 11.73/1.98      | v4_relat_1(X0,X1) != iProver_top
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_4997,plain,
% 11.73/1.98      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_3364,c_1722]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3317,plain,
% 11.73/1.98      ( ~ v4_relat_1(sK2,X0)
% 11.73/1.98      | ~ v1_relat_1(sK2)
% 11.73/1.98      | k7_relat_1(sK2,X0) = sK2 ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_11]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3318,plain,
% 11.73/1.98      ( k7_relat_1(sK2,X0) = sK2
% 11.73/1.98      | v4_relat_1(sK2,X0) != iProver_top
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_3317]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_3320,plain,
% 11.73/1.98      ( k7_relat_1(sK2,sK0) = sK2
% 11.73/1.98      | v4_relat_1(sK2,sK0) != iProver_top
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(instantiation,[status(thm)],[c_3318]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_7051,plain,
% 11.73/1.98      ( k7_relat_1(sK2,sK0) = sK2 ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_4997,c_48,c_2124,c_2253,c_3320,c_3364]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8,plain,
% 11.73/1.98      ( ~ v1_relat_1(X0)
% 11.73/1.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.73/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1725,plain,
% 11.73/1.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5211,plain,
% 11.73/1.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5207,c_1725]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_7053,plain,
% 11.73/1.98      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_7051,c_5211]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_7054,plain,
% 11.73/1.98      ( k9_relat_1(sK2,sK0) = sK1 ),
% 11.73/1.98      inference(light_normalisation,[status(thm)],[c_7053,c_3890]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10,plain,
% 11.73/1.98      ( ~ v1_relat_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X1)
% 11.73/1.98      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 11.73/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1723,plain,
% 11.73/1.98      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 11.73/1.98      | v1_relat_1(X0) != iProver_top
% 11.73/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_6545,plain,
% 11.73/1.98      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5207,c_1723]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8787,plain,
% 11.73/1.98      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5063,c_6545]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8790,plain,
% 11.73/1.98      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
% 11.73/1.98      inference(light_normalisation,[status(thm)],[c_8787,c_8536]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_14,plain,
% 11.73/1.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.73/1.98      inference(cnf_transformation,[],[f124]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_8791,plain,
% 11.73/1.98      ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
% 11.73/1.98      inference(demodulation,[status(thm)],[c_8790,c_14]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10194,plain,
% 11.73/1.98      ( k1_relat_1(sK3) = sK1 | v1_relat_1(sK3) != iProver_top ),
% 11.73/1.98      inference(light_normalisation,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_10187,c_7054,c_8791]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10316,plain,
% 11.73/1.98      ( k1_relat_1(sK3) = sK1 ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_10194,c_50,c_2788,c_2966]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_15,plain,
% 11.73/1.98      ( ~ v1_relat_1(X0)
% 11.73/1.98      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 11.73/1.98      inference(cnf_transformation,[],[f125]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1720,plain,
% 11.73/1.98      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5070,plain,
% 11.73/1.98      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5063,c_1720]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10321,plain,
% 11.73/1.98      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 11.73/1.98      inference(demodulation,[status(thm)],[c_10316,c_5070]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1,plain,
% 11.73/1.98      ( r1_tarski(X0,X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f131]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1731,plain,
% 11.73/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_16,plain,
% 11.73/1.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 11.73/1.98      inference(cnf_transformation,[],[f126]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1719,plain,
% 11.73/1.98      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 11.73/1.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5479,plain,
% 11.73/1.98      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_1731,c_1719]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10441,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_7167,c_5479]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_23,plain,
% 11.73/1.98      ( ~ v2_funct_1(X0)
% 11.73/1.98      | ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f99]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_664,plain,
% 11.73/1.98      ( ~ v1_funct_1(X0)
% 11.73/1.98      | ~ v1_relat_1(X0)
% 11.73/1.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.73/1.98      | sK2 != X0 ),
% 11.73/1.98      inference(resolution_lifted,[status(thm)],[c_23,c_40]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_665,plain,
% 11.73/1.98      ( ~ v1_funct_1(sK2)
% 11.73/1.98      | ~ v1_relat_1(sK2)
% 11.73/1.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.73/1.98      inference(unflattening,[status(thm)],[c_664]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_667,plain,
% 11.73/1.98      ( ~ v1_relat_1(sK2)
% 11.73/1.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.73/1.98      inference(global_propositional_subsumption,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_665,c_46]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1694,plain,
% 11.73/1.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5215,plain,
% 11.73/1.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5207,c_1694]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10442,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
% 11.73/1.98      inference(light_normalisation,[status(thm)],[c_10441,c_5215]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10318,plain,
% 11.73/1.98      ( k10_relat_1(sK2,sK1) = sK0 ),
% 11.73/1.98      inference(demodulation,[status(thm)],[c_10316,c_8791]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_9,plain,
% 11.73/1.98      ( ~ v1_relat_1(X0)
% 11.73/1.98      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 11.73/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_1724,plain,
% 11.73/1.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 11.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5213,plain,
% 11.73/1.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 11.73/1.98      inference(superposition,[status(thm)],[c_5207,c_1724]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_5216,plain,
% 11.73/1.98      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 11.73/1.98      inference(light_normalisation,[status(thm)],[c_5213,c_3890]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10335,plain,
% 11.73/1.98      ( k1_relat_1(sK2) = sK0 ),
% 11.73/1.98      inference(demodulation,[status(thm)],[c_10318,c_5216]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_10443,plain,
% 11.73/1.98      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 11.73/1.98      inference(demodulation,[status(thm)],[c_10442,c_10335]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_35794,plain,
% 11.73/1.98      ( k2_funct_1(sK2) = sK3 ),
% 11.73/1.98      inference(light_normalisation,
% 11.73/1.98                [status(thm)],
% 11.73/1.98                [c_35785,c_8536,c_10321,c_10443]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(c_37,negated_conjecture,
% 11.73/1.98      ( k2_funct_1(sK2) != sK3 ),
% 11.73/1.98      inference(cnf_transformation,[],[f122]) ).
% 11.73/1.98  
% 11.73/1.98  cnf(contradiction,plain,
% 11.73/1.98      ( $false ),
% 11.73/1.98      inference(minisat,[status(thm)],[c_35794,c_37]) ).
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.73/1.98  
% 11.73/1.98  ------                               Statistics
% 11.73/1.98  
% 11.73/1.98  ------ General
% 11.73/1.98  
% 11.73/1.98  abstr_ref_over_cycles:                  0
% 11.73/1.98  abstr_ref_under_cycles:                 0
% 11.73/1.98  gc_basic_clause_elim:                   0
% 11.73/1.98  forced_gc_time:                         0
% 11.73/1.98  parsing_time:                           0.015
% 11.73/1.98  unif_index_cands_time:                  0.
% 11.73/1.98  unif_index_add_time:                    0.
% 11.73/1.98  orderings_time:                         0.
% 11.73/1.98  out_proof_time:                         0.022
% 11.73/1.98  total_time:                             1.131
% 11.73/1.98  num_of_symbols:                         55
% 11.73/1.98  num_of_terms:                           47052
% 11.73/1.98  
% 11.73/1.98  ------ Preprocessing
% 11.73/1.98  
% 11.73/1.98  num_of_splits:                          0
% 11.73/1.98  num_of_split_atoms:                     0
% 11.73/1.98  num_of_reused_defs:                     0
% 11.73/1.98  num_eq_ax_congr_red:                    15
% 11.73/1.98  num_of_sem_filtered_clauses:            1
% 11.73/1.98  num_of_subtypes:                        0
% 11.73/1.98  monotx_restored_types:                  0
% 11.73/1.98  sat_num_of_epr_types:                   0
% 11.73/1.98  sat_num_of_non_cyclic_types:            0
% 11.73/1.98  sat_guarded_non_collapsed_types:        0
% 11.73/1.98  num_pure_diseq_elim:                    0
% 11.73/1.98  simp_replaced_by:                       0
% 11.73/1.98  res_preprocessed:                       218
% 11.73/1.98  prep_upred:                             0
% 11.73/1.98  prep_unflattend:                        18
% 11.73/1.98  smt_new_axioms:                         0
% 11.73/1.98  pred_elim_cands:                        5
% 11.73/1.98  pred_elim:                              2
% 11.73/1.98  pred_elim_cl:                           -1
% 11.73/1.98  pred_elim_cycles:                       5
% 11.73/1.98  merged_defs:                            0
% 11.73/1.98  merged_defs_ncl:                        0
% 11.73/1.98  bin_hyper_res:                          0
% 11.73/1.98  prep_cycles:                            4
% 11.73/1.98  pred_elim_time:                         0.007
% 11.73/1.98  splitting_time:                         0.
% 11.73/1.98  sem_filter_time:                        0.
% 11.73/1.98  monotx_time:                            0.001
% 11.73/1.98  subtype_inf_time:                       0.
% 11.73/1.98  
% 11.73/1.98  ------ Problem properties
% 11.73/1.98  
% 11.73/1.98  clauses:                                46
% 11.73/1.98  conjectures:                            8
% 11.73/1.98  epr:                                    6
% 11.73/1.98  horn:                                   46
% 11.73/1.98  ground:                                 13
% 11.73/1.98  unary:                                  14
% 11.73/1.98  binary:                                 15
% 11.73/1.98  lits:                                   103
% 11.73/1.98  lits_eq:                                29
% 11.73/1.98  fd_pure:                                0
% 11.73/1.98  fd_pseudo:                              0
% 11.73/1.98  fd_cond:                                0
% 11.73/1.98  fd_pseudo_cond:                         1
% 11.73/1.98  ac_symbols:                             0
% 11.73/1.98  
% 11.73/1.98  ------ Propositional Solver
% 11.73/1.98  
% 11.73/1.98  prop_solver_calls:                      36
% 11.73/1.98  prop_fast_solver_calls:                 2224
% 11.73/1.98  smt_solver_calls:                       0
% 11.73/1.98  smt_fast_solver_calls:                  0
% 11.73/1.98  prop_num_of_clauses:                    18938
% 11.73/1.98  prop_preprocess_simplified:             35461
% 11.73/1.98  prop_fo_subsumed:                       146
% 11.73/1.98  prop_solver_time:                       0.
% 11.73/1.98  smt_solver_time:                        0.
% 11.73/1.98  smt_fast_solver_time:                   0.
% 11.73/1.98  prop_fast_solver_time:                  0.
% 11.73/1.98  prop_unsat_core_time:                   0.003
% 11.73/1.98  
% 11.73/1.98  ------ QBF
% 11.73/1.98  
% 11.73/1.98  qbf_q_res:                              0
% 11.73/1.98  qbf_num_tautologies:                    0
% 11.73/1.98  qbf_prep_cycles:                        0
% 11.73/1.98  
% 11.73/1.98  ------ BMC1
% 11.73/1.98  
% 11.73/1.98  bmc1_current_bound:                     -1
% 11.73/1.98  bmc1_last_solved_bound:                 -1
% 11.73/1.98  bmc1_unsat_core_size:                   -1
% 11.73/1.98  bmc1_unsat_core_parents_size:           -1
% 11.73/1.98  bmc1_merge_next_fun:                    0
% 11.73/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.73/1.98  
% 11.73/1.98  ------ Instantiation
% 11.73/1.98  
% 11.73/1.98  inst_num_of_clauses:                    5549
% 11.73/1.98  inst_num_in_passive:                    2252
% 11.73/1.98  inst_num_in_active:                     2269
% 11.73/1.98  inst_num_in_unprocessed:                1028
% 11.73/1.98  inst_num_of_loops:                      2400
% 11.73/1.98  inst_num_of_learning_restarts:          0
% 11.73/1.98  inst_num_moves_active_passive:          127
% 11.73/1.98  inst_lit_activity:                      0
% 11.73/1.98  inst_lit_activity_moves:                2
% 11.73/1.98  inst_num_tautologies:                   0
% 11.73/1.98  inst_num_prop_implied:                  0
% 11.73/1.98  inst_num_existing_simplified:           0
% 11.73/1.98  inst_num_eq_res_simplified:             0
% 11.73/1.98  inst_num_child_elim:                    0
% 11.73/1.98  inst_num_of_dismatching_blockings:      1721
% 11.73/1.98  inst_num_of_non_proper_insts:           5608
% 11.73/1.98  inst_num_of_duplicates:                 0
% 11.73/1.98  inst_inst_num_from_inst_to_res:         0
% 11.73/1.98  inst_dismatching_checking_time:         0.
% 11.73/1.98  
% 11.73/1.98  ------ Resolution
% 11.73/1.98  
% 11.73/1.98  res_num_of_clauses:                     0
% 11.73/1.98  res_num_in_passive:                     0
% 11.73/1.98  res_num_in_active:                      0
% 11.73/1.98  res_num_of_loops:                       222
% 11.73/1.98  res_forward_subset_subsumed:            369
% 11.73/1.98  res_backward_subset_subsumed:           0
% 11.73/1.98  res_forward_subsumed:                   0
% 11.73/1.98  res_backward_subsumed:                  0
% 11.73/1.98  res_forward_subsumption_resolution:     1
% 11.73/1.98  res_backward_subsumption_resolution:    0
% 11.73/1.98  res_clause_to_clause_subsumption:       2319
% 11.73/1.98  res_orphan_elimination:                 0
% 11.73/1.98  res_tautology_del:                      355
% 11.73/1.98  res_num_eq_res_simplified:              0
% 11.73/1.98  res_num_sel_changes:                    0
% 11.73/1.98  res_moves_from_active_to_pass:          0
% 11.73/1.98  
% 11.73/1.98  ------ Superposition
% 11.73/1.98  
% 11.73/1.98  sup_time_total:                         0.
% 11.73/1.98  sup_time_generating:                    0.
% 11.73/1.98  sup_time_sim_full:                      0.
% 11.73/1.98  sup_time_sim_immed:                     0.
% 11.73/1.98  
% 11.73/1.98  sup_num_of_clauses:                     1022
% 11.73/1.98  sup_num_in_active:                      422
% 11.73/1.98  sup_num_in_passive:                     600
% 11.73/1.98  sup_num_of_loops:                       479
% 11.73/1.98  sup_fw_superposition:                   887
% 11.73/1.98  sup_bw_superposition:                   446
% 11.73/1.98  sup_immediate_simplified:               497
% 11.73/1.98  sup_given_eliminated:                   1
% 11.73/1.98  comparisons_done:                       0
% 11.73/1.98  comparisons_avoided:                    0
% 11.73/1.98  
% 11.73/1.98  ------ Simplifications
% 11.73/1.98  
% 11.73/1.98  
% 11.73/1.98  sim_fw_subset_subsumed:                 27
% 11.73/1.98  sim_bw_subset_subsumed:                 27
% 11.73/1.98  sim_fw_subsumed:                        71
% 11.73/1.98  sim_bw_subsumed:                        3
% 11.73/1.98  sim_fw_subsumption_res:                 0
% 11.73/1.98  sim_bw_subsumption_res:                 0
% 11.73/1.98  sim_tautology_del:                      11
% 11.73/1.98  sim_eq_tautology_del:                   142
% 11.73/1.98  sim_eq_res_simp:                        0
% 11.73/1.98  sim_fw_demodulated:                     114
% 11.73/1.98  sim_bw_demodulated:                     57
% 11.73/1.98  sim_light_normalised:                   434
% 11.73/1.98  sim_joinable_taut:                      0
% 11.73/1.98  sim_joinable_simp:                      0
% 11.73/1.98  sim_ac_normalised:                      0
% 11.73/1.98  sim_smt_subsumption:                    0
% 11.73/1.98  
%------------------------------------------------------------------------------
