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
% DateTime   : Thu Dec  3 12:03:10 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  233 (1220 expanded)
%              Number of clauses        :  136 ( 349 expanded)
%              Number of leaves         :   26 ( 312 expanded)
%              Depth                    :   19
%              Number of atoms          :  854 (9750 expanded)
%              Number of equality atoms :  412 (3584 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f70,plain,(
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
     => ( k2_funct_1(X2) != sK4
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
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
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & k2_relset_1(sK1,sK2,sK3) = sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f65,f70,f69])).

fof(f115,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f71])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f71])).

fof(f110,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f71])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f118,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f120,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f71])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f91,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f25,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f85,f102])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f92,f102])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f122,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f83,f102])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f56])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f52])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f117,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f71])).

fof(f23,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f26,axiom,(
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

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f114,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f119,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f71])).

fof(f16,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f126,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f89,f102])).

fof(f27,axiom,(
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

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f106,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f102])).

fof(f121,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1529,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1542,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3064,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1542])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1526,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_3065,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_1542])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1524,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1549,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1552,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5888,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1552])).

cnf(c_19077,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_5888])).

cnf(c_19935,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19077,c_3065])).

cnf(c_19936,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_19935])).

cnf(c_19943,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK3),sK3),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3065,c_19936])).

cnf(c_42,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1532,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1559,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1558,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2711,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1559,c_1558])).

cnf(c_3756,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1532,c_2711])).

cnf(c_3760,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_3756])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1625,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1720,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_1858,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1720])).

cnf(c_4603,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3760,c_48,c_47,c_46,c_42,c_40,c_38,c_1858])).

cnf(c_19949,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19943,c_4603])).

cnf(c_19976,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,sK4)) = k5_relat_1(k6_partfun1(sK2),sK4) ),
    inference(superposition,[status(thm)],[c_3064,c_19949])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1555,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1555,c_4])).

cnf(c_1530,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1546,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4512,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1546])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_5137,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4512,c_49,c_3065])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k5_relat_1(X2,k6_partfun1(X3)) = X2
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_476,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_1523,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_5139,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5137,c_1523])).

cnf(c_5144,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(k1_relat_1(sK3))) = k2_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_5139])).

cnf(c_3071,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3065])).

cnf(c_5145,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | k5_relat_1(k2_funct_1(sK3),k6_partfun1(k1_relat_1(sK3))) = k2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5144])).

cnf(c_5351,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5776,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(k1_relat_1(sK3))) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5144,c_48,c_3071,c_5145,c_5351])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1543,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5490,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1543])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1531,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3358,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1531,c_2711])).

cnf(c_3362,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_3358])).

cnf(c_1626,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1746,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_1871,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_3484,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3362,c_48,c_47,c_46,c_42,c_40,c_38,c_1871])).

cnf(c_5491,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5490,c_3484])).

cnf(c_5556,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5491,c_49,c_3065])).

cnf(c_10,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_5567,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5556,c_10])).

cnf(c_5568,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_5567,c_10])).

cnf(c_5778,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(sK1)) = k2_funct_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5776,c_5568])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1537,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5943,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1537])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_52,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_5981,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5943,c_52])).

cnf(c_5982,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5981])).

cnf(c_5989,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_5982])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_41,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_532,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_28,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_540,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_532,c_28])).

cnf(c_1521,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1804,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2518,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1521,c_48,c_46,c_45,c_43,c_540,c_1804])).

cnf(c_5991,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5989,c_2518])).

cnf(c_6242,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5991,c_49])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_544,plain,
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
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_545,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_639,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_545])).

cnf(c_1520,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_2019,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1520])).

cnf(c_50,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_53,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2525,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2019,c_49,c_50,c_51,c_52,c_53,c_54])).

cnf(c_3363,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_3358])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1643,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_871,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1693,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_1980,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK1 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_3177,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3178,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3177])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1535,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6449,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | o_0_0_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1535,c_2711])).

cnf(c_6451,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_6449])).

cnf(c_6621,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6451,c_49,c_50,c_51])).

cnf(c_6622,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6621])).

cnf(c_6627,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2518,c_6622])).

cnf(c_10060,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3363,c_52,c_53,c_54,c_39,c_0,c_1643,c_1980,c_3178,c_6627])).

cnf(c_6654,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6627,c_52,c_53,c_54,c_39,c_0,c_1643,c_1980,c_3178])).

cnf(c_6660,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6654,c_1543])).

cnf(c_7693,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6660,c_52,c_3064])).

cnf(c_10062,plain,
    ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK2) ),
    inference(demodulation,[status(thm)],[c_10060,c_7693])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1551,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3221,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK4)),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_3064,c_1551])).

cnf(c_10277,plain,
    ( k5_relat_1(k6_partfun1(sK2),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_10062,c_3221])).

cnf(c_19985,plain,
    ( k2_funct_1(sK3) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_19976,c_5778,c_6242,c_10277])).

cnf(c_37,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f121])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19985,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:25:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.97/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/1.51  
% 7.97/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.51  
% 7.97/1.51  ------  iProver source info
% 7.97/1.51  
% 7.97/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.51  git: non_committed_changes: false
% 7.97/1.51  git: last_make_outside_of_git: false
% 7.97/1.51  
% 7.97/1.51  ------ 
% 7.97/1.51  
% 7.97/1.51  ------ Input Options
% 7.97/1.51  
% 7.97/1.51  --out_options                           all
% 7.97/1.51  --tptp_safe_out                         true
% 7.97/1.51  --problem_path                          ""
% 7.97/1.51  --include_path                          ""
% 7.97/1.51  --clausifier                            res/vclausify_rel
% 7.97/1.51  --clausifier_options                    ""
% 7.97/1.51  --stdin                                 false
% 7.97/1.51  --stats_out                             all
% 7.97/1.51  
% 7.97/1.51  ------ General Options
% 7.97/1.51  
% 7.97/1.51  --fof                                   false
% 7.97/1.51  --time_out_real                         305.
% 7.97/1.51  --time_out_virtual                      -1.
% 7.97/1.51  --symbol_type_check                     false
% 7.97/1.51  --clausify_out                          false
% 7.97/1.51  --sig_cnt_out                           false
% 7.97/1.51  --trig_cnt_out                          false
% 7.97/1.51  --trig_cnt_out_tolerance                1.
% 7.97/1.51  --trig_cnt_out_sk_spl                   false
% 7.97/1.51  --abstr_cl_out                          false
% 7.97/1.51  
% 7.97/1.51  ------ Global Options
% 7.97/1.51  
% 7.97/1.51  --schedule                              default
% 7.97/1.51  --add_important_lit                     false
% 7.97/1.51  --prop_solver_per_cl                    1000
% 7.97/1.51  --min_unsat_core                        false
% 7.97/1.51  --soft_assumptions                      false
% 7.97/1.51  --soft_lemma_size                       3
% 7.97/1.51  --prop_impl_unit_size                   0
% 7.97/1.51  --prop_impl_unit                        []
% 7.97/1.51  --share_sel_clauses                     true
% 7.97/1.51  --reset_solvers                         false
% 7.97/1.51  --bc_imp_inh                            [conj_cone]
% 7.97/1.51  --conj_cone_tolerance                   3.
% 7.97/1.51  --extra_neg_conj                        none
% 7.97/1.51  --large_theory_mode                     true
% 7.97/1.51  --prolific_symb_bound                   200
% 7.97/1.51  --lt_threshold                          2000
% 7.97/1.51  --clause_weak_htbl                      true
% 7.97/1.51  --gc_record_bc_elim                     false
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing Options
% 7.97/1.51  
% 7.97/1.51  --preprocessing_flag                    true
% 7.97/1.51  --time_out_prep_mult                    0.1
% 7.97/1.51  --splitting_mode                        input
% 7.97/1.51  --splitting_grd                         true
% 7.97/1.51  --splitting_cvd                         false
% 7.97/1.51  --splitting_cvd_svl                     false
% 7.97/1.51  --splitting_nvd                         32
% 7.97/1.51  --sub_typing                            true
% 7.97/1.51  --prep_gs_sim                           true
% 7.97/1.51  --prep_unflatten                        true
% 7.97/1.51  --prep_res_sim                          true
% 7.97/1.51  --prep_upred                            true
% 7.97/1.51  --prep_sem_filter                       exhaustive
% 7.97/1.51  --prep_sem_filter_out                   false
% 7.97/1.51  --pred_elim                             true
% 7.97/1.51  --res_sim_input                         true
% 7.97/1.51  --eq_ax_congr_red                       true
% 7.97/1.51  --pure_diseq_elim                       true
% 7.97/1.51  --brand_transform                       false
% 7.97/1.51  --non_eq_to_eq                          false
% 7.97/1.51  --prep_def_merge                        true
% 7.97/1.51  --prep_def_merge_prop_impl              false
% 7.97/1.51  --prep_def_merge_mbd                    true
% 7.97/1.51  --prep_def_merge_tr_red                 false
% 7.97/1.51  --prep_def_merge_tr_cl                  false
% 7.97/1.51  --smt_preprocessing                     true
% 7.97/1.51  --smt_ac_axioms                         fast
% 7.97/1.51  --preprocessed_out                      false
% 7.97/1.51  --preprocessed_stats                    false
% 7.97/1.51  
% 7.97/1.51  ------ Abstraction refinement Options
% 7.97/1.51  
% 7.97/1.51  --abstr_ref                             []
% 7.97/1.51  --abstr_ref_prep                        false
% 7.97/1.51  --abstr_ref_until_sat                   false
% 7.97/1.51  --abstr_ref_sig_restrict                funpre
% 7.97/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.51  --abstr_ref_under                       []
% 7.97/1.51  
% 7.97/1.51  ------ SAT Options
% 7.97/1.51  
% 7.97/1.51  --sat_mode                              false
% 7.97/1.51  --sat_fm_restart_options                ""
% 7.97/1.51  --sat_gr_def                            false
% 7.97/1.51  --sat_epr_types                         true
% 7.97/1.51  --sat_non_cyclic_types                  false
% 7.97/1.51  --sat_finite_models                     false
% 7.97/1.51  --sat_fm_lemmas                         false
% 7.97/1.51  --sat_fm_prep                           false
% 7.97/1.51  --sat_fm_uc_incr                        true
% 7.97/1.51  --sat_out_model                         small
% 7.97/1.51  --sat_out_clauses                       false
% 7.97/1.51  
% 7.97/1.51  ------ QBF Options
% 7.97/1.51  
% 7.97/1.51  --qbf_mode                              false
% 7.97/1.51  --qbf_elim_univ                         false
% 7.97/1.51  --qbf_dom_inst                          none
% 7.97/1.51  --qbf_dom_pre_inst                      false
% 7.97/1.51  --qbf_sk_in                             false
% 7.97/1.51  --qbf_pred_elim                         true
% 7.97/1.51  --qbf_split                             512
% 7.97/1.51  
% 7.97/1.51  ------ BMC1 Options
% 7.97/1.51  
% 7.97/1.51  --bmc1_incremental                      false
% 7.97/1.51  --bmc1_axioms                           reachable_all
% 7.97/1.51  --bmc1_min_bound                        0
% 7.97/1.51  --bmc1_max_bound                        -1
% 7.97/1.51  --bmc1_max_bound_default                -1
% 7.97/1.51  --bmc1_symbol_reachability              true
% 7.97/1.51  --bmc1_property_lemmas                  false
% 7.97/1.51  --bmc1_k_induction                      false
% 7.97/1.51  --bmc1_non_equiv_states                 false
% 7.97/1.51  --bmc1_deadlock                         false
% 7.97/1.51  --bmc1_ucm                              false
% 7.97/1.51  --bmc1_add_unsat_core                   none
% 7.97/1.51  --bmc1_unsat_core_children              false
% 7.97/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.51  --bmc1_out_stat                         full
% 7.97/1.51  --bmc1_ground_init                      false
% 7.97/1.51  --bmc1_pre_inst_next_state              false
% 7.97/1.51  --bmc1_pre_inst_state                   false
% 7.97/1.51  --bmc1_pre_inst_reach_state             false
% 7.97/1.51  --bmc1_out_unsat_core                   false
% 7.97/1.51  --bmc1_aig_witness_out                  false
% 7.97/1.51  --bmc1_verbose                          false
% 7.97/1.51  --bmc1_dump_clauses_tptp                false
% 7.97/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.51  --bmc1_dump_file                        -
% 7.97/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.51  --bmc1_ucm_extend_mode                  1
% 7.97/1.51  --bmc1_ucm_init_mode                    2
% 7.97/1.51  --bmc1_ucm_cone_mode                    none
% 7.97/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.51  --bmc1_ucm_relax_model                  4
% 7.97/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.51  --bmc1_ucm_layered_model                none
% 7.97/1.51  --bmc1_ucm_max_lemma_size               10
% 7.97/1.51  
% 7.97/1.51  ------ AIG Options
% 7.97/1.51  
% 7.97/1.51  --aig_mode                              false
% 7.97/1.51  
% 7.97/1.51  ------ Instantiation Options
% 7.97/1.51  
% 7.97/1.51  --instantiation_flag                    true
% 7.97/1.51  --inst_sos_flag                         true
% 7.97/1.51  --inst_sos_phase                        true
% 7.97/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.51  --inst_lit_sel_side                     num_symb
% 7.97/1.51  --inst_solver_per_active                1400
% 7.97/1.51  --inst_solver_calls_frac                1.
% 7.97/1.51  --inst_passive_queue_type               priority_queues
% 7.97/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.51  --inst_passive_queues_freq              [25;2]
% 7.97/1.51  --inst_dismatching                      true
% 7.97/1.51  --inst_eager_unprocessed_to_passive     true
% 7.97/1.51  --inst_prop_sim_given                   true
% 7.97/1.51  --inst_prop_sim_new                     false
% 7.97/1.51  --inst_subs_new                         false
% 7.97/1.51  --inst_eq_res_simp                      false
% 7.97/1.51  --inst_subs_given                       false
% 7.97/1.51  --inst_orphan_elimination               true
% 7.97/1.51  --inst_learning_loop_flag               true
% 7.97/1.51  --inst_learning_start                   3000
% 7.97/1.51  --inst_learning_factor                  2
% 7.97/1.51  --inst_start_prop_sim_after_learn       3
% 7.97/1.51  --inst_sel_renew                        solver
% 7.97/1.51  --inst_lit_activity_flag                true
% 7.97/1.51  --inst_restr_to_given                   false
% 7.97/1.51  --inst_activity_threshold               500
% 7.97/1.51  --inst_out_proof                        true
% 7.97/1.51  
% 7.97/1.51  ------ Resolution Options
% 7.97/1.51  
% 7.97/1.51  --resolution_flag                       true
% 7.97/1.51  --res_lit_sel                           adaptive
% 7.97/1.51  --res_lit_sel_side                      none
% 7.97/1.51  --res_ordering                          kbo
% 7.97/1.51  --res_to_prop_solver                    active
% 7.97/1.51  --res_prop_simpl_new                    false
% 7.97/1.51  --res_prop_simpl_given                  true
% 7.97/1.51  --res_passive_queue_type                priority_queues
% 7.97/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.51  --res_passive_queues_freq               [15;5]
% 7.97/1.51  --res_forward_subs                      full
% 7.97/1.51  --res_backward_subs                     full
% 7.97/1.51  --res_forward_subs_resolution           true
% 7.97/1.51  --res_backward_subs_resolution          true
% 7.97/1.51  --res_orphan_elimination                true
% 7.97/1.51  --res_time_limit                        2.
% 7.97/1.51  --res_out_proof                         true
% 7.97/1.51  
% 7.97/1.51  ------ Superposition Options
% 7.97/1.51  
% 7.97/1.51  --superposition_flag                    true
% 7.97/1.51  --sup_passive_queue_type                priority_queues
% 7.97/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.51  --demod_completeness_check              fast
% 7.97/1.51  --demod_use_ground                      true
% 7.97/1.51  --sup_to_prop_solver                    passive
% 7.97/1.51  --sup_prop_simpl_new                    true
% 7.97/1.51  --sup_prop_simpl_given                  true
% 7.97/1.51  --sup_fun_splitting                     true
% 7.97/1.51  --sup_smt_interval                      50000
% 7.97/1.51  
% 7.97/1.51  ------ Superposition Simplification Setup
% 7.97/1.51  
% 7.97/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.51  --sup_immed_triv                        [TrivRules]
% 7.97/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.51  --sup_immed_bw_main                     []
% 7.97/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.51  --sup_input_bw                          []
% 7.97/1.51  
% 7.97/1.51  ------ Combination Options
% 7.97/1.51  
% 7.97/1.51  --comb_res_mult                         3
% 7.97/1.51  --comb_sup_mult                         2
% 7.97/1.51  --comb_inst_mult                        10
% 7.97/1.51  
% 7.97/1.51  ------ Debug Options
% 7.97/1.51  
% 7.97/1.51  --dbg_backtrace                         false
% 7.97/1.51  --dbg_dump_prop_clauses                 false
% 7.97/1.51  --dbg_dump_prop_clauses_file            -
% 7.97/1.51  --dbg_out_stat                          false
% 7.97/1.51  ------ Parsing...
% 7.97/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.97/1.51  ------ Proving...
% 7.97/1.51  ------ Problem Properties 
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  clauses                                 47
% 7.97/1.51  conjectures                             11
% 7.97/1.51  EPR                                     11
% 7.97/1.51  Horn                                    43
% 7.97/1.51  unary                                   19
% 7.97/1.51  binary                                  6
% 7.97/1.51  lits                                    153
% 7.97/1.51  lits eq                                 38
% 7.97/1.51  fd_pure                                 0
% 7.97/1.51  fd_pseudo                               0
% 7.97/1.51  fd_cond                                 5
% 7.97/1.51  fd_pseudo_cond                          1
% 7.97/1.51  AC symbols                              0
% 7.97/1.51  
% 7.97/1.51  ------ Schedule dynamic 5 is on 
% 7.97/1.51  
% 7.97/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  ------ 
% 7.97/1.51  Current options:
% 7.97/1.51  ------ 
% 7.97/1.51  
% 7.97/1.51  ------ Input Options
% 7.97/1.51  
% 7.97/1.51  --out_options                           all
% 7.97/1.51  --tptp_safe_out                         true
% 7.97/1.51  --problem_path                          ""
% 7.97/1.51  --include_path                          ""
% 7.97/1.51  --clausifier                            res/vclausify_rel
% 7.97/1.51  --clausifier_options                    ""
% 7.97/1.51  --stdin                                 false
% 7.97/1.51  --stats_out                             all
% 7.97/1.51  
% 7.97/1.51  ------ General Options
% 7.97/1.51  
% 7.97/1.51  --fof                                   false
% 7.97/1.51  --time_out_real                         305.
% 7.97/1.51  --time_out_virtual                      -1.
% 7.97/1.51  --symbol_type_check                     false
% 7.97/1.51  --clausify_out                          false
% 7.97/1.51  --sig_cnt_out                           false
% 7.97/1.51  --trig_cnt_out                          false
% 7.97/1.51  --trig_cnt_out_tolerance                1.
% 7.97/1.51  --trig_cnt_out_sk_spl                   false
% 7.97/1.51  --abstr_cl_out                          false
% 7.97/1.51  
% 7.97/1.51  ------ Global Options
% 7.97/1.51  
% 7.97/1.51  --schedule                              default
% 7.97/1.51  --add_important_lit                     false
% 7.97/1.51  --prop_solver_per_cl                    1000
% 7.97/1.51  --min_unsat_core                        false
% 7.97/1.51  --soft_assumptions                      false
% 7.97/1.51  --soft_lemma_size                       3
% 7.97/1.51  --prop_impl_unit_size                   0
% 7.97/1.51  --prop_impl_unit                        []
% 7.97/1.51  --share_sel_clauses                     true
% 7.97/1.51  --reset_solvers                         false
% 7.97/1.51  --bc_imp_inh                            [conj_cone]
% 7.97/1.51  --conj_cone_tolerance                   3.
% 7.97/1.51  --extra_neg_conj                        none
% 7.97/1.51  --large_theory_mode                     true
% 7.97/1.51  --prolific_symb_bound                   200
% 7.97/1.51  --lt_threshold                          2000
% 7.97/1.51  --clause_weak_htbl                      true
% 7.97/1.51  --gc_record_bc_elim                     false
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing Options
% 7.97/1.51  
% 7.97/1.51  --preprocessing_flag                    true
% 7.97/1.51  --time_out_prep_mult                    0.1
% 7.97/1.51  --splitting_mode                        input
% 7.97/1.51  --splitting_grd                         true
% 7.97/1.51  --splitting_cvd                         false
% 7.97/1.51  --splitting_cvd_svl                     false
% 7.97/1.51  --splitting_nvd                         32
% 7.97/1.51  --sub_typing                            true
% 7.97/1.51  --prep_gs_sim                           true
% 7.97/1.51  --prep_unflatten                        true
% 7.97/1.51  --prep_res_sim                          true
% 7.97/1.51  --prep_upred                            true
% 7.97/1.51  --prep_sem_filter                       exhaustive
% 7.97/1.51  --prep_sem_filter_out                   false
% 7.97/1.51  --pred_elim                             true
% 7.97/1.51  --res_sim_input                         true
% 7.97/1.51  --eq_ax_congr_red                       true
% 7.97/1.51  --pure_diseq_elim                       true
% 7.97/1.51  --brand_transform                       false
% 7.97/1.51  --non_eq_to_eq                          false
% 7.97/1.51  --prep_def_merge                        true
% 7.97/1.51  --prep_def_merge_prop_impl              false
% 7.97/1.51  --prep_def_merge_mbd                    true
% 7.97/1.51  --prep_def_merge_tr_red                 false
% 7.97/1.51  --prep_def_merge_tr_cl                  false
% 7.97/1.51  --smt_preprocessing                     true
% 7.97/1.51  --smt_ac_axioms                         fast
% 7.97/1.51  --preprocessed_out                      false
% 7.97/1.51  --preprocessed_stats                    false
% 7.97/1.51  
% 7.97/1.51  ------ Abstraction refinement Options
% 7.97/1.51  
% 7.97/1.51  --abstr_ref                             []
% 7.97/1.51  --abstr_ref_prep                        false
% 7.97/1.51  --abstr_ref_until_sat                   false
% 7.97/1.51  --abstr_ref_sig_restrict                funpre
% 7.97/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.51  --abstr_ref_under                       []
% 7.97/1.51  
% 7.97/1.51  ------ SAT Options
% 7.97/1.51  
% 7.97/1.51  --sat_mode                              false
% 7.97/1.51  --sat_fm_restart_options                ""
% 7.97/1.51  --sat_gr_def                            false
% 7.97/1.51  --sat_epr_types                         true
% 7.97/1.51  --sat_non_cyclic_types                  false
% 7.97/1.51  --sat_finite_models                     false
% 7.97/1.51  --sat_fm_lemmas                         false
% 7.97/1.51  --sat_fm_prep                           false
% 7.97/1.51  --sat_fm_uc_incr                        true
% 7.97/1.51  --sat_out_model                         small
% 7.97/1.51  --sat_out_clauses                       false
% 7.97/1.51  
% 7.97/1.51  ------ QBF Options
% 7.97/1.51  
% 7.97/1.51  --qbf_mode                              false
% 7.97/1.51  --qbf_elim_univ                         false
% 7.97/1.51  --qbf_dom_inst                          none
% 7.97/1.51  --qbf_dom_pre_inst                      false
% 7.97/1.51  --qbf_sk_in                             false
% 7.97/1.51  --qbf_pred_elim                         true
% 7.97/1.51  --qbf_split                             512
% 7.97/1.51  
% 7.97/1.51  ------ BMC1 Options
% 7.97/1.51  
% 7.97/1.51  --bmc1_incremental                      false
% 7.97/1.51  --bmc1_axioms                           reachable_all
% 7.97/1.51  --bmc1_min_bound                        0
% 7.97/1.51  --bmc1_max_bound                        -1
% 7.97/1.51  --bmc1_max_bound_default                -1
% 7.97/1.51  --bmc1_symbol_reachability              true
% 7.97/1.51  --bmc1_property_lemmas                  false
% 7.97/1.51  --bmc1_k_induction                      false
% 7.97/1.51  --bmc1_non_equiv_states                 false
% 7.97/1.51  --bmc1_deadlock                         false
% 7.97/1.51  --bmc1_ucm                              false
% 7.97/1.51  --bmc1_add_unsat_core                   none
% 7.97/1.51  --bmc1_unsat_core_children              false
% 7.97/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.51  --bmc1_out_stat                         full
% 7.97/1.51  --bmc1_ground_init                      false
% 7.97/1.51  --bmc1_pre_inst_next_state              false
% 7.97/1.51  --bmc1_pre_inst_state                   false
% 7.97/1.51  --bmc1_pre_inst_reach_state             false
% 7.97/1.51  --bmc1_out_unsat_core                   false
% 7.97/1.51  --bmc1_aig_witness_out                  false
% 7.97/1.51  --bmc1_verbose                          false
% 7.97/1.51  --bmc1_dump_clauses_tptp                false
% 7.97/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.51  --bmc1_dump_file                        -
% 7.97/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.51  --bmc1_ucm_extend_mode                  1
% 7.97/1.51  --bmc1_ucm_init_mode                    2
% 7.97/1.51  --bmc1_ucm_cone_mode                    none
% 7.97/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.51  --bmc1_ucm_relax_model                  4
% 7.97/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.51  --bmc1_ucm_layered_model                none
% 7.97/1.51  --bmc1_ucm_max_lemma_size               10
% 7.97/1.51  
% 7.97/1.51  ------ AIG Options
% 7.97/1.51  
% 7.97/1.51  --aig_mode                              false
% 7.97/1.51  
% 7.97/1.51  ------ Instantiation Options
% 7.97/1.51  
% 7.97/1.51  --instantiation_flag                    true
% 7.97/1.51  --inst_sos_flag                         true
% 7.97/1.51  --inst_sos_phase                        true
% 7.97/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.51  --inst_lit_sel_side                     none
% 7.97/1.51  --inst_solver_per_active                1400
% 7.97/1.51  --inst_solver_calls_frac                1.
% 7.97/1.51  --inst_passive_queue_type               priority_queues
% 7.97/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.51  --inst_passive_queues_freq              [25;2]
% 7.97/1.51  --inst_dismatching                      true
% 7.97/1.51  --inst_eager_unprocessed_to_passive     true
% 7.97/1.51  --inst_prop_sim_given                   true
% 7.97/1.51  --inst_prop_sim_new                     false
% 7.97/1.51  --inst_subs_new                         false
% 7.97/1.51  --inst_eq_res_simp                      false
% 7.97/1.51  --inst_subs_given                       false
% 7.97/1.51  --inst_orphan_elimination               true
% 7.97/1.51  --inst_learning_loop_flag               true
% 7.97/1.51  --inst_learning_start                   3000
% 7.97/1.51  --inst_learning_factor                  2
% 7.97/1.51  --inst_start_prop_sim_after_learn       3
% 7.97/1.51  --inst_sel_renew                        solver
% 7.97/1.51  --inst_lit_activity_flag                true
% 7.97/1.51  --inst_restr_to_given                   false
% 7.97/1.51  --inst_activity_threshold               500
% 7.97/1.51  --inst_out_proof                        true
% 7.97/1.51  
% 7.97/1.51  ------ Resolution Options
% 7.97/1.51  
% 7.97/1.51  --resolution_flag                       false
% 7.97/1.51  --res_lit_sel                           adaptive
% 7.97/1.51  --res_lit_sel_side                      none
% 7.97/1.51  --res_ordering                          kbo
% 7.97/1.51  --res_to_prop_solver                    active
% 7.97/1.51  --res_prop_simpl_new                    false
% 7.97/1.51  --res_prop_simpl_given                  true
% 7.97/1.51  --res_passive_queue_type                priority_queues
% 7.97/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.51  --res_passive_queues_freq               [15;5]
% 7.97/1.51  --res_forward_subs                      full
% 7.97/1.51  --res_backward_subs                     full
% 7.97/1.51  --res_forward_subs_resolution           true
% 7.97/1.51  --res_backward_subs_resolution          true
% 7.97/1.51  --res_orphan_elimination                true
% 7.97/1.51  --res_time_limit                        2.
% 7.97/1.51  --res_out_proof                         true
% 7.97/1.51  
% 7.97/1.51  ------ Superposition Options
% 7.97/1.51  
% 7.97/1.51  --superposition_flag                    true
% 7.97/1.51  --sup_passive_queue_type                priority_queues
% 7.97/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.51  --demod_completeness_check              fast
% 7.97/1.51  --demod_use_ground                      true
% 7.97/1.51  --sup_to_prop_solver                    passive
% 7.97/1.51  --sup_prop_simpl_new                    true
% 7.97/1.51  --sup_prop_simpl_given                  true
% 7.97/1.51  --sup_fun_splitting                     true
% 7.97/1.51  --sup_smt_interval                      50000
% 7.97/1.51  
% 7.97/1.51  ------ Superposition Simplification Setup
% 7.97/1.51  
% 7.97/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.51  --sup_immed_triv                        [TrivRules]
% 7.97/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.51  --sup_immed_bw_main                     []
% 7.97/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.51  --sup_input_bw                          []
% 7.97/1.51  
% 7.97/1.51  ------ Combination Options
% 7.97/1.51  
% 7.97/1.51  --comb_res_mult                         3
% 7.97/1.51  --comb_sup_mult                         2
% 7.97/1.51  --comb_inst_mult                        10
% 7.97/1.51  
% 7.97/1.51  ------ Debug Options
% 7.97/1.51  
% 7.97/1.51  --dbg_backtrace                         false
% 7.97/1.51  --dbg_dump_prop_clauses                 false
% 7.97/1.51  --dbg_dump_prop_clauses_file            -
% 7.97/1.51  --dbg_out_stat                          false
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  ------ Proving...
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  % SZS status Theorem for theBenchmark.p
% 7.97/1.51  
% 7.97/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.51  
% 7.97/1.51  fof(f29,conjecture,(
% 7.97/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f30,negated_conjecture,(
% 7.97/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.97/1.51    inference(negated_conjecture,[],[f29])).
% 7.97/1.51  
% 7.97/1.51  fof(f64,plain,(
% 7.97/1.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.97/1.51    inference(ennf_transformation,[],[f30])).
% 7.97/1.51  
% 7.97/1.51  fof(f65,plain,(
% 7.97/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.97/1.51    inference(flattening,[],[f64])).
% 7.97/1.51  
% 7.97/1.51  fof(f70,plain,(
% 7.97/1.51    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 7.97/1.51    introduced(choice_axiom,[])).
% 7.97/1.51  
% 7.97/1.51  fof(f69,plain,(
% 7.97/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.97/1.51    introduced(choice_axiom,[])).
% 7.97/1.51  
% 7.97/1.51  fof(f71,plain,(
% 7.97/1.51    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.97/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f65,f70,f69])).
% 7.97/1.51  
% 7.97/1.51  fof(f115,plain,(
% 7.97/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.97/1.51    inference(cnf_transformation,[],[f71])).
% 7.97/1.51  
% 7.97/1.51  fof(f19,axiom,(
% 7.97/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f50,plain,(
% 7.97/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.51    inference(ennf_transformation,[],[f19])).
% 7.97/1.51  
% 7.97/1.51  fof(f94,plain,(
% 7.97/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f50])).
% 7.97/1.51  
% 7.97/1.51  fof(f112,plain,(
% 7.97/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.97/1.51    inference(cnf_transformation,[],[f71])).
% 7.97/1.51  
% 7.97/1.51  fof(f110,plain,(
% 7.97/1.51    v1_funct_1(sK3)),
% 7.97/1.51    inference(cnf_transformation,[],[f71])).
% 7.97/1.51  
% 7.97/1.51  fof(f14,axiom,(
% 7.97/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f42,plain,(
% 7.97/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.97/1.51    inference(ennf_transformation,[],[f14])).
% 7.97/1.51  
% 7.97/1.51  fof(f43,plain,(
% 7.97/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.97/1.51    inference(flattening,[],[f42])).
% 7.97/1.51  
% 7.97/1.51  fof(f86,plain,(
% 7.97/1.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f43])).
% 7.97/1.51  
% 7.97/1.51  fof(f10,axiom,(
% 7.97/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f38,plain,(
% 7.97/1.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.97/1.52    inference(ennf_transformation,[],[f10])).
% 7.97/1.52  
% 7.97/1.52  fof(f81,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f38])).
% 7.97/1.52  
% 7.97/1.52  fof(f116,plain,(
% 7.97/1.52    k2_relset_1(sK1,sK2,sK3) = sK2),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f28,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f62,plain,(
% 7.97/1.52    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.97/1.52    inference(ennf_transformation,[],[f28])).
% 7.97/1.52  
% 7.97/1.52  fof(f63,plain,(
% 7.97/1.52    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.97/1.52    inference(flattening,[],[f62])).
% 7.97/1.52  
% 7.97/1.52  fof(f109,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f63])).
% 7.97/1.52  
% 7.97/1.52  fof(f1,axiom,(
% 7.97/1.52    v1_xboole_0(o_0_0_xboole_0)),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f72,plain,(
% 7.97/1.52    v1_xboole_0(o_0_0_xboole_0)),
% 7.97/1.52    inference(cnf_transformation,[],[f1])).
% 7.97/1.52  
% 7.97/1.52  fof(f2,axiom,(
% 7.97/1.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f33,plain,(
% 7.97/1.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.97/1.52    inference(ennf_transformation,[],[f2])).
% 7.97/1.52  
% 7.97/1.52  fof(f73,plain,(
% 7.97/1.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f33])).
% 7.97/1.52  
% 7.97/1.52  fof(f111,plain,(
% 7.97/1.52    v1_funct_2(sK3,sK1,sK2)),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f118,plain,(
% 7.97/1.52    v2_funct_1(sK3)),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f120,plain,(
% 7.97/1.52    k1_xboole_0 != sK2),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f6,axiom,(
% 7.97/1.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f77,plain,(
% 7.97/1.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f6])).
% 7.97/1.52  
% 7.97/1.52  fof(f5,axiom,(
% 7.97/1.52    ! [X0] : k2_subset_1(X0) = X0),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f76,plain,(
% 7.97/1.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.97/1.52    inference(cnf_transformation,[],[f5])).
% 7.97/1.52  
% 7.97/1.52  fof(f17,axiom,(
% 7.97/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f46,plain,(
% 7.97/1.52    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.97/1.52    inference(ennf_transformation,[],[f17])).
% 7.97/1.52  
% 7.97/1.52  fof(f47,plain,(
% 7.97/1.52    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.97/1.52    inference(flattening,[],[f46])).
% 7.97/1.52  
% 7.97/1.52  fof(f91,plain,(
% 7.97/1.52    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f47])).
% 7.97/1.52  
% 7.97/1.52  fof(f7,axiom,(
% 7.97/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f31,plain,(
% 7.97/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 7.97/1.52    inference(unused_predicate_definition_removal,[],[f7])).
% 7.97/1.52  
% 7.97/1.52  fof(f35,plain,(
% 7.97/1.52    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.97/1.52    inference(ennf_transformation,[],[f31])).
% 7.97/1.52  
% 7.97/1.52  fof(f78,plain,(
% 7.97/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f35])).
% 7.97/1.52  
% 7.97/1.52  fof(f13,axiom,(
% 7.97/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f40,plain,(
% 7.97/1.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.97/1.52    inference(ennf_transformation,[],[f13])).
% 7.97/1.52  
% 7.97/1.52  fof(f41,plain,(
% 7.97/1.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.97/1.52    inference(flattening,[],[f40])).
% 7.97/1.52  
% 7.97/1.52  fof(f85,plain,(
% 7.97/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f41])).
% 7.97/1.52  
% 7.97/1.52  fof(f25,axiom,(
% 7.97/1.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f102,plain,(
% 7.97/1.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f25])).
% 7.97/1.52  
% 7.97/1.52  fof(f125,plain,(
% 7.97/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.97/1.52    inference(definition_unfolding,[],[f85,f102])).
% 7.97/1.52  
% 7.97/1.52  fof(f18,axiom,(
% 7.97/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f48,plain,(
% 7.97/1.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.97/1.52    inference(ennf_transformation,[],[f18])).
% 7.97/1.52  
% 7.97/1.52  fof(f49,plain,(
% 7.97/1.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.97/1.52    inference(flattening,[],[f48])).
% 7.97/1.52  
% 7.97/1.52  fof(f92,plain,(
% 7.97/1.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f49])).
% 7.97/1.52  
% 7.97/1.52  fof(f128,plain,(
% 7.97/1.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.97/1.52    inference(definition_unfolding,[],[f92,f102])).
% 7.97/1.52  
% 7.97/1.52  fof(f108,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f63])).
% 7.97/1.52  
% 7.97/1.52  fof(f11,axiom,(
% 7.97/1.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f83,plain,(
% 7.97/1.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.97/1.52    inference(cnf_transformation,[],[f11])).
% 7.97/1.52  
% 7.97/1.52  fof(f122,plain,(
% 7.97/1.52    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.97/1.52    inference(definition_unfolding,[],[f83,f102])).
% 7.97/1.52  
% 7.97/1.52  fof(f24,axiom,(
% 7.97/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f56,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.97/1.52    inference(ennf_transformation,[],[f24])).
% 7.97/1.52  
% 7.97/1.52  fof(f57,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.97/1.52    inference(flattening,[],[f56])).
% 7.97/1.52  
% 7.97/1.52  fof(f101,plain,(
% 7.97/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f57])).
% 7.97/1.52  
% 7.97/1.52  fof(f113,plain,(
% 7.97/1.52    v1_funct_1(sK4)),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f21,axiom,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f52,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.97/1.52    inference(ennf_transformation,[],[f21])).
% 7.97/1.52  
% 7.97/1.52  fof(f53,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(flattening,[],[f52])).
% 7.97/1.52  
% 7.97/1.52  fof(f68,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(nnf_transformation,[],[f53])).
% 7.97/1.52  
% 7.97/1.52  fof(f96,plain,(
% 7.97/1.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f68])).
% 7.97/1.52  
% 7.97/1.52  fof(f117,plain,(
% 7.97/1.52    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f23,axiom,(
% 7.97/1.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f32,plain,(
% 7.97/1.52    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.97/1.52    inference(pure_predicate_removal,[],[f23])).
% 7.97/1.52  
% 7.97/1.52  fof(f100,plain,(
% 7.97/1.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f32])).
% 7.97/1.52  
% 7.97/1.52  fof(f22,axiom,(
% 7.97/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f54,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.97/1.52    inference(ennf_transformation,[],[f22])).
% 7.97/1.52  
% 7.97/1.52  fof(f55,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.97/1.52    inference(flattening,[],[f54])).
% 7.97/1.52  
% 7.97/1.52  fof(f99,plain,(
% 7.97/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f55])).
% 7.97/1.52  
% 7.97/1.52  fof(f26,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f58,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.97/1.52    inference(ennf_transformation,[],[f26])).
% 7.97/1.52  
% 7.97/1.52  fof(f59,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.97/1.52    inference(flattening,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f103,plain,(
% 7.97/1.52    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f59])).
% 7.97/1.52  
% 7.97/1.52  fof(f114,plain,(
% 7.97/1.52    v1_funct_2(sK4,sK2,sK1)),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f119,plain,(
% 7.97/1.52    k1_xboole_0 != sK1),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  fof(f16,axiom,(
% 7.97/1.52    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f89,plain,(
% 7.97/1.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f16])).
% 7.97/1.52  
% 7.97/1.52  fof(f126,plain,(
% 7.97/1.52    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.97/1.52    inference(definition_unfolding,[],[f89,f102])).
% 7.97/1.52  
% 7.97/1.52  fof(f27,axiom,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f60,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.97/1.52    inference(ennf_transformation,[],[f27])).
% 7.97/1.52  
% 7.97/1.52  fof(f61,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.97/1.52    inference(flattening,[],[f60])).
% 7.97/1.52  
% 7.97/1.52  fof(f106,plain,(
% 7.97/1.52    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f61])).
% 7.97/1.52  
% 7.97/1.52  fof(f12,axiom,(
% 7.97/1.52    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f39,plain,(
% 7.97/1.52    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.97/1.52    inference(ennf_transformation,[],[f12])).
% 7.97/1.52  
% 7.97/1.52  fof(f84,plain,(
% 7.97/1.52    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f39])).
% 7.97/1.52  
% 7.97/1.52  fof(f124,plain,(
% 7.97/1.52    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.97/1.52    inference(definition_unfolding,[],[f84,f102])).
% 7.97/1.52  
% 7.97/1.52  fof(f121,plain,(
% 7.97/1.52    k2_funct_1(sK3) != sK4),
% 7.97/1.52    inference(cnf_transformation,[],[f71])).
% 7.97/1.52  
% 7.97/1.52  cnf(c_43,negated_conjecture,
% 7.97/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.97/1.52      inference(cnf_transformation,[],[f115]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1529,plain,
% 7.97/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_22,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | v1_relat_1(X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1542,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3064,plain,
% 7.97/1.52      ( v1_relat_1(sK4) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1529,c_1542]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_46,negated_conjecture,
% 7.97/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.97/1.52      inference(cnf_transformation,[],[f112]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1526,plain,
% 7.97/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3065,plain,
% 7.97/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1526,c_1542]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_48,negated_conjecture,
% 7.97/1.52      ( v1_funct_1(sK3) ),
% 7.97/1.52      inference(cnf_transformation,[],[f110]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1524,plain,
% 7.97/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_15,plain,
% 7.97/1.52      ( ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_relat_1(X0)
% 7.97/1.52      | v1_relat_1(k2_funct_1(X0)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1549,plain,
% 7.97/1.52      ( v1_funct_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_9,plain,
% 7.97/1.52      ( ~ v1_relat_1(X0)
% 7.97/1.52      | ~ v1_relat_1(X1)
% 7.97/1.52      | ~ v1_relat_1(X2)
% 7.97/1.52      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1552,plain,
% 7.97/1.52      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.97/1.52      | v1_relat_1(X1) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X2) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5888,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.97/1.52      | v1_funct_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X1) != iProver_top
% 7.97/1.52      | v1_relat_1(X2) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1549,c_1552]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19077,plain,
% 7.97/1.52      ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
% 7.97/1.52      | v1_relat_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X1) != iProver_top
% 7.97/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1524,c_5888]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19935,plain,
% 7.97/1.52      ( v1_relat_1(X1) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top
% 7.97/1.52      | k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1)) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_19077,c_3065]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19936,plain,
% 7.97/1.52      ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
% 7.97/1.52      | v1_relat_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_19935]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19943,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK3),sK3),X0)
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_3065,c_19936]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_42,negated_conjecture,
% 7.97/1.52      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ v2_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | k2_relset_1(X1,X2,X0) != X2
% 7.97/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.97/1.52      | k1_xboole_0 = X2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f109]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1532,plain,
% 7.97/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 7.97/1.52      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.97/1.52      | k1_xboole_0 = X1
% 7.97/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v2_funct_1(X2) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_0,plain,
% 7.97/1.52      ( v1_xboole_0(o_0_0_xboole_0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1559,plain,
% 7.97/1.52      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1,plain,
% 7.97/1.52      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1558,plain,
% 7.97/1.52      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2711,plain,
% 7.97/1.52      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1559,c_1558]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3756,plain,
% 7.97/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 7.97/1.52      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.97/1.52      | o_0_0_xboole_0 = X1
% 7.97/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v2_funct_1(X2) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_1532,c_2711]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3760,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 7.97/1.52      | sK2 = o_0_0_xboole_0
% 7.97/1.52      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.97/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.97/1.52      | v2_funct_1(sK3) != iProver_top
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_42,c_3756]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_47,negated_conjecture,
% 7.97/1.52      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.97/1.52      inference(cnf_transformation,[],[f111]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_40,negated_conjecture,
% 7.97/1.52      ( v2_funct_1(sK3) ),
% 7.97/1.52      inference(cnf_transformation,[],[f118]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_38,negated_conjecture,
% 7.97/1.52      ( k1_xboole_0 != sK2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f120]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1625,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,sK2)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 7.97/1.52      | ~ v2_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | k2_relset_1(X1,sK2,X0) != sK2
% 7.97/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK2)
% 7.97/1.52      | k1_xboole_0 = sK2 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_35]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1720,plain,
% 7.97/1.52      ( ~ v1_funct_2(sK3,X0,sK2)
% 7.97/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 7.97/1.52      | ~ v2_funct_1(sK3)
% 7.97/1.52      | ~ v1_funct_1(sK3)
% 7.97/1.52      | k2_relset_1(X0,sK2,sK3) != sK2
% 7.97/1.52      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 7.97/1.52      | k1_xboole_0 = sK2 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1625]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1858,plain,
% 7.97/1.52      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.97/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.97/1.52      | ~ v2_funct_1(sK3)
% 7.97/1.52      | ~ v1_funct_1(sK3)
% 7.97/1.52      | k2_relset_1(sK1,sK2,sK3) != sK2
% 7.97/1.52      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 7.97/1.52      | k1_xboole_0 = sK2 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1720]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_4603,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_3760,c_48,c_47,c_46,c_42,c_40,c_38,c_1858]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19949,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK2),X0)
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_19943,c_4603]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19976,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,sK4)) = k5_relat_1(k6_partfun1(sK2),sK4) ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_3064,c_19949]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5,plain,
% 7.97/1.52      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1555,plain,
% 7.97/1.52      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_4,plain,
% 7.97/1.52      ( k2_subset_1(X0) = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1560,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_1555,c_4]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1530,plain,
% 7.97/1.52      ( v2_funct_1(sK3) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_18,plain,
% 7.97/1.52      ( ~ v2_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_relat_1(X0)
% 7.97/1.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1546,plain,
% 7.97/1.52      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.97/1.52      | v2_funct_1(X0) != iProver_top
% 7.97/1.52      | v1_funct_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_4512,plain,
% 7.97/1.52      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top
% 7.97/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1530,c_1546]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_49,plain,
% 7.97/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5137,plain,
% 7.97/1.52      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_4512,c_49,c_3065]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6,plain,
% 7.97/1.52      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_13,plain,
% 7.97/1.52      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.97/1.52      | ~ v1_relat_1(X0)
% 7.97/1.52      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f125]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_475,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.52      | ~ v1_relat_1(X2)
% 7.97/1.52      | X3 != X1
% 7.97/1.52      | k5_relat_1(X2,k6_partfun1(X3)) = X2
% 7.97/1.52      | k2_relat_1(X2) != X0 ),
% 7.97/1.52      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_476,plain,
% 7.97/1.52      ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 7.97/1.52      | ~ v1_relat_1(X0)
% 7.97/1.52      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.97/1.52      inference(unflattening,[status(thm)],[c_475]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1523,plain,
% 7.97/1.52      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 7.97/1.52      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1)) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5139,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
% 7.97/1.52      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top
% 7.97/1.52      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5137,c_1523]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5144,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(k1_relat_1(sK3))) = k2_funct_1(sK3)
% 7.97/1.52      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1560,c_5139]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3071,plain,
% 7.97/1.52      ( v1_relat_1(sK3) ),
% 7.97/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_3065]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5145,plain,
% 7.97/1.52      ( ~ v1_relat_1(k2_funct_1(sK3))
% 7.97/1.52      | k5_relat_1(k2_funct_1(sK3),k6_partfun1(k1_relat_1(sK3))) = k2_funct_1(sK3) ),
% 7.97/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_5144]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5351,plain,
% 7.97/1.52      ( ~ v1_funct_1(sK3)
% 7.97/1.52      | v1_relat_1(k2_funct_1(sK3))
% 7.97/1.52      | ~ v1_relat_1(sK3) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_15]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5776,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(k1_relat_1(sK3))) = k2_funct_1(sK3) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_5144,c_48,c_3071,c_5145,c_5351]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_21,plain,
% 7.97/1.52      ( ~ v2_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_relat_1(X0)
% 7.97/1.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f128]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1543,plain,
% 7.97/1.52      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.97/1.52      | v2_funct_1(X0) != iProver_top
% 7.97/1.52      | v1_funct_1(X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5490,plain,
% 7.97/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top
% 7.97/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1530,c_1543]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ v2_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | k2_relset_1(X1,X2,X0) != X2
% 7.97/1.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.97/1.52      | k1_xboole_0 = X2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f108]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1531,plain,
% 7.97/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 7.97/1.52      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.97/1.52      | k1_xboole_0 = X1
% 7.97/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v2_funct_1(X2) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3358,plain,
% 7.97/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 7.97/1.52      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.97/1.52      | o_0_0_xboole_0 = X1
% 7.97/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v2_funct_1(X2) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_1531,c_2711]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3362,plain,
% 7.97/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.97/1.52      | sK2 = o_0_0_xboole_0
% 7.97/1.52      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.97/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.97/1.52      | v2_funct_1(sK3) != iProver_top
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_42,c_3358]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1626,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,sK2)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 7.97/1.52      | ~ v2_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | k2_relset_1(X1,sK2,X0) != sK2
% 7.97/1.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.97/1.52      | k1_xboole_0 = sK2 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_36]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1746,plain,
% 7.97/1.52      ( ~ v1_funct_2(sK3,X0,sK2)
% 7.97/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 7.97/1.52      | ~ v2_funct_1(sK3)
% 7.97/1.52      | ~ v1_funct_1(sK3)
% 7.97/1.52      | k2_relset_1(X0,sK2,sK3) != sK2
% 7.97/1.52      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
% 7.97/1.52      | k1_xboole_0 = sK2 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1626]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1871,plain,
% 7.97/1.52      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.97/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.97/1.52      | ~ v2_funct_1(sK3)
% 7.97/1.52      | ~ v1_funct_1(sK3)
% 7.97/1.52      | k2_relset_1(sK1,sK2,sK3) != sK2
% 7.97/1.52      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.97/1.52      | k1_xboole_0 = sK2 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1746]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3484,plain,
% 7.97/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_3362,c_48,c_47,c_46,c_42,c_40,c_38,c_1871]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5491,plain,
% 7.97/1.52      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top
% 7.97/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_5490,c_3484]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5556,plain,
% 7.97/1.52      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_5491,c_49,c_3065]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_10,plain,
% 7.97/1.52      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f122]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5567,plain,
% 7.97/1.52      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5556,c_10]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5568,plain,
% 7.97/1.52      ( k1_relat_1(sK3) = sK1 ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_5567,c_10]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5778,plain,
% 7.97/1.52      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(sK1)) = k2_funct_1(sK3) ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_5776,c_5568]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_29,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X3)
% 7.97/1.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1537,plain,
% 7.97/1.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.97/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.97/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v1_funct_1(X5) != iProver_top
% 7.97/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5943,plain,
% 7.97/1.52      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top
% 7.97/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1529,c_1537]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_45,negated_conjecture,
% 7.97/1.52      ( v1_funct_1(sK4) ),
% 7.97/1.52      inference(cnf_transformation,[],[f113]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_52,plain,
% 7.97/1.52      ( v1_funct_1(sK4) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5981,plain,
% 7.97/1.52      ( v1_funct_1(X2) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_5943,c_52]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5982,plain,
% 7.97/1.52      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_5981]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5989,plain,
% 7.97/1.52      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1526,c_5982]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_25,plain,
% 7.97/1.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.97/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.97/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.97/1.52      | X3 = X2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_41,negated_conjecture,
% 7.97/1.52      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f117]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_531,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | X3 = X0
% 7.97/1.52      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 7.97/1.52      | k6_partfun1(sK1) != X3
% 7.97/1.52      | sK1 != X2
% 7.97/1.52      | sK1 != X1 ),
% 7.97/1.52      inference(resolution_lifted,[status(thm)],[c_25,c_41]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_532,plain,
% 7.97/1.52      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.97/1.52      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.97/1.52      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 7.97/1.52      inference(unflattening,[status(thm)],[c_531]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_28,plain,
% 7.97/1.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.97/1.52      inference(cnf_transformation,[],[f100]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_540,plain,
% 7.97/1.52      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.97/1.52      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 7.97/1.52      inference(forward_subsumption_resolution,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_532,c_28]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1521,plain,
% 7.97/1.52      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.97/1.52      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_26,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.97/1.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X3) ),
% 7.97/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1804,plain,
% 7.97/1.52      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.97/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.97/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.97/1.52      | ~ v1_funct_1(sK4)
% 7.97/1.52      | ~ v1_funct_1(sK3) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_26]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2518,plain,
% 7.97/1.52      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_1521,c_48,c_46,c_45,c_43,c_540,c_1804]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5991,plain,
% 7.97/1.52      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_5989,c_2518]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6242,plain,
% 7.97/1.52      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_5991,c_49]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_30,plain,
% 7.97/1.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.97/1.52      | ~ v1_funct_2(X2,X0,X1)
% 7.97/1.52      | ~ v1_funct_2(X3,X1,X0)
% 7.97/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.97/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.97/1.52      | ~ v1_funct_1(X2)
% 7.97/1.52      | ~ v1_funct_1(X3)
% 7.97/1.52      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_544,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.97/1.52      | ~ v1_funct_2(X3,X2,X1)
% 7.97/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X3)
% 7.97/1.52      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.97/1.52      | k2_relset_1(X1,X2,X0) = X2
% 7.97/1.52      | k6_partfun1(X2) != k6_partfun1(sK1)
% 7.97/1.52      | sK1 != X2 ),
% 7.97/1.52      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_545,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,sK1)
% 7.97/1.52      | ~ v1_funct_2(X2,sK1,X1)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.97/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X2)
% 7.97/1.52      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.97/1.52      | k2_relset_1(X1,sK1,X0) = sK1
% 7.97/1.52      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 7.97/1.52      inference(unflattening,[status(thm)],[c_544]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_639,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,sK1)
% 7.97/1.52      | ~ v1_funct_2(X2,sK1,X1)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.97/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X2)
% 7.97/1.52      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.97/1.52      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 7.97/1.52      inference(equality_resolution_simp,[status(thm)],[c_545]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1520,plain,
% 7.97/1.52      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.97/1.52      | k2_relset_1(X0,sK1,X2) = sK1
% 7.97/1.52      | v1_funct_2(X2,X0,sK1) != iProver_top
% 7.97/1.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.97/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top
% 7.97/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2019,plain,
% 7.97/1.52      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 7.97/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.97/1.52      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.97/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.97/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.97/1.52      | v1_funct_1(sK4) != iProver_top
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.97/1.52      inference(equality_resolution,[status(thm)],[c_1520]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_50,plain,
% 7.97/1.52      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_51,plain,
% 7.97/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_44,negated_conjecture,
% 7.97/1.52      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f114]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_53,plain,
% 7.97/1.52      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_54,plain,
% 7.97/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2525,plain,
% 7.97/1.52      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_2019,c_49,c_50,c_51,c_52,c_53,c_54]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3363,plain,
% 7.97/1.52      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 7.97/1.52      | sK1 = o_0_0_xboole_0
% 7.97/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.97/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.97/1.52      | v2_funct_1(sK4) != iProver_top
% 7.97/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_2525,c_3358]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_39,negated_conjecture,
% 7.97/1.52      ( k1_xboole_0 != sK1 ),
% 7.97/1.52      inference(cnf_transformation,[],[f119]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1643,plain,
% 7.97/1.52      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_871,plain,
% 7.97/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.97/1.52      theory(equality) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1693,plain,
% 7.97/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_871]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1980,plain,
% 7.97/1.52      ( v1_xboole_0(sK1)
% 7.97/1.52      | ~ v1_xboole_0(o_0_0_xboole_0)
% 7.97/1.52      | sK1 != o_0_0_xboole_0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1693]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_17,plain,
% 7.97/1.52      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f126]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3177,plain,
% 7.97/1.52      ( v2_funct_1(k6_partfun1(sK1)) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_17]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3178,plain,
% 7.97/1.52      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_3177]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_32,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.97/1.52      | ~ v1_funct_2(X3,X4,X1)
% 7.97/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | v2_funct_1(X0)
% 7.97/1.52      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | ~ v1_funct_1(X3)
% 7.97/1.52      | k2_relset_1(X4,X1,X3) != X1
% 7.97/1.52      | k1_xboole_0 = X2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f106]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1535,plain,
% 7.97/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 7.97/1.52      | k1_xboole_0 = X3
% 7.97/1.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.97/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.97/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v2_funct_1(X4) = iProver_top
% 7.97/1.52      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.97/1.52      | v1_funct_1(X4) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6449,plain,
% 7.97/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 7.97/1.52      | o_0_0_xboole_0 = X3
% 7.97/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.97/1.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.97/1.52      | v2_funct_1(X4) = iProver_top
% 7.97/1.52      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top
% 7.97/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_1535,c_2711]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6451,plain,
% 7.97/1.52      ( o_0_0_xboole_0 = X0
% 7.97/1.52      | v1_funct_2(X1,sK2,X0) != iProver_top
% 7.97/1.52      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.97/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.97/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.97/1.52      | v2_funct_1(X1) = iProver_top
% 7.97/1.52      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 7.97/1.52      | v1_funct_1(X1) != iProver_top
% 7.97/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_42,c_6449]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6621,plain,
% 7.97/1.52      ( v1_funct_1(X1) != iProver_top
% 7.97/1.52      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 7.97/1.52      | v2_funct_1(X1) = iProver_top
% 7.97/1.52      | v1_funct_2(X1,sK2,X0) != iProver_top
% 7.97/1.52      | o_0_0_xboole_0 = X0
% 7.97/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_6451,c_49,c_50,c_51]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6622,plain,
% 7.97/1.52      ( o_0_0_xboole_0 = X0
% 7.97/1.52      | v1_funct_2(X1,sK2,X0) != iProver_top
% 7.97/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.97/1.52      | v2_funct_1(X1) = iProver_top
% 7.97/1.52      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 7.97/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_6621]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6627,plain,
% 7.97/1.52      ( sK1 = o_0_0_xboole_0
% 7.97/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.97/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.97/1.52      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 7.97/1.52      | v2_funct_1(sK4) = iProver_top
% 7.97/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_2518,c_6622]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_10060,plain,
% 7.97/1.52      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_3363,c_52,c_53,c_54,c_39,c_0,c_1643,c_1980,c_3178,
% 7.97/1.52                 c_6627]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6654,plain,
% 7.97/1.52      ( v2_funct_1(sK4) = iProver_top ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_6627,c_52,c_53,c_54,c_39,c_0,c_1643,c_1980,c_3178]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6660,plain,
% 7.97/1.52      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
% 7.97/1.52      | v1_funct_1(sK4) != iProver_top
% 7.97/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_6654,c_1543]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_7693,plain,
% 7.97/1.52      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_6660,c_52,c_3064]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_10062,plain,
% 7.97/1.52      ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK2) ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_10060,c_7693]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12,plain,
% 7.97/1.52      ( ~ v1_relat_1(X0)
% 7.97/1.52      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f124]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1551,plain,
% 7.97/1.52      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3221,plain,
% 7.97/1.52      ( k5_relat_1(k6_partfun1(k1_relat_1(sK4)),sK4) = sK4 ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_3064,c_1551]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_10277,plain,
% 7.97/1.52      ( k5_relat_1(k6_partfun1(sK2),sK4) = sK4 ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_10062,c_3221]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19985,plain,
% 7.97/1.52      ( k2_funct_1(sK3) = sK4 ),
% 7.97/1.52      inference(light_normalisation,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_19976,c_5778,c_6242,c_10277]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_37,negated_conjecture,
% 7.97/1.52      ( k2_funct_1(sK3) != sK4 ),
% 7.97/1.52      inference(cnf_transformation,[],[f121]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(contradiction,plain,
% 7.97/1.52      ( $false ),
% 7.97/1.52      inference(minisat,[status(thm)],[c_19985,c_37]) ).
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.52  
% 7.97/1.52  ------                               Statistics
% 7.97/1.52  
% 7.97/1.52  ------ General
% 7.97/1.52  
% 7.97/1.52  abstr_ref_over_cycles:                  0
% 7.97/1.52  abstr_ref_under_cycles:                 0
% 7.97/1.52  gc_basic_clause_elim:                   0
% 7.97/1.52  forced_gc_time:                         0
% 7.97/1.52  parsing_time:                           0.007
% 7.97/1.52  unif_index_cands_time:                  0.
% 7.97/1.52  unif_index_add_time:                    0.
% 7.97/1.52  orderings_time:                         0.
% 7.97/1.52  out_proof_time:                         0.018
% 7.97/1.52  total_time:                             0.786
% 7.97/1.52  num_of_symbols:                         58
% 7.97/1.52  num_of_terms:                           35880
% 7.97/1.52  
% 7.97/1.52  ------ Preprocessing
% 7.97/1.52  
% 7.97/1.52  num_of_splits:                          0
% 7.97/1.52  num_of_split_atoms:                     0
% 7.97/1.52  num_of_reused_defs:                     0
% 7.97/1.52  num_eq_ax_congr_red:                    7
% 7.97/1.52  num_of_sem_filtered_clauses:            1
% 7.97/1.52  num_of_subtypes:                        0
% 7.97/1.52  monotx_restored_types:                  0
% 7.97/1.52  sat_num_of_epr_types:                   0
% 7.97/1.52  sat_num_of_non_cyclic_types:            0
% 7.97/1.52  sat_guarded_non_collapsed_types:        0
% 7.97/1.52  num_pure_diseq_elim:                    0
% 7.97/1.52  simp_replaced_by:                       0
% 7.97/1.52  res_preprocessed:                       229
% 7.97/1.52  prep_upred:                             0
% 7.97/1.52  prep_unflattend:                        14
% 7.97/1.52  smt_new_axioms:                         0
% 7.97/1.52  pred_elim_cands:                        6
% 7.97/1.52  pred_elim:                              2
% 7.97/1.52  pred_elim_cl:                           2
% 7.97/1.52  pred_elim_cycles:                       4
% 7.97/1.52  merged_defs:                            0
% 7.97/1.52  merged_defs_ncl:                        0
% 7.97/1.52  bin_hyper_res:                          0
% 7.97/1.52  prep_cycles:                            4
% 7.97/1.52  pred_elim_time:                         0.004
% 7.97/1.52  splitting_time:                         0.
% 7.97/1.52  sem_filter_time:                        0.
% 7.97/1.52  monotx_time:                            0.
% 7.97/1.52  subtype_inf_time:                       0.
% 7.97/1.52  
% 7.97/1.52  ------ Problem properties
% 7.97/1.52  
% 7.97/1.52  clauses:                                47
% 7.97/1.52  conjectures:                            11
% 7.97/1.52  epr:                                    11
% 7.97/1.52  horn:                                   43
% 7.97/1.52  ground:                                 14
% 7.97/1.52  unary:                                  19
% 7.97/1.52  binary:                                 6
% 7.97/1.52  lits:                                   153
% 7.97/1.52  lits_eq:                                38
% 7.97/1.52  fd_pure:                                0
% 7.97/1.52  fd_pseudo:                              0
% 7.97/1.52  fd_cond:                                5
% 7.97/1.52  fd_pseudo_cond:                         1
% 7.97/1.52  ac_symbols:                             0
% 7.97/1.52  
% 7.97/1.52  ------ Propositional Solver
% 7.97/1.52  
% 7.97/1.52  prop_solver_calls:                      32
% 7.97/1.52  prop_fast_solver_calls:                 2326
% 7.97/1.52  smt_solver_calls:                       0
% 7.97/1.52  smt_fast_solver_calls:                  0
% 7.97/1.52  prop_num_of_clauses:                    10999
% 7.97/1.52  prop_preprocess_simplified:             21068
% 7.97/1.52  prop_fo_subsumed:                       145
% 7.97/1.52  prop_solver_time:                       0.
% 7.97/1.52  smt_solver_time:                        0.
% 7.97/1.52  smt_fast_solver_time:                   0.
% 7.97/1.52  prop_fast_solver_time:                  0.
% 7.97/1.52  prop_unsat_core_time:                   0.001
% 7.97/1.52  
% 7.97/1.52  ------ QBF
% 7.97/1.52  
% 7.97/1.52  qbf_q_res:                              0
% 7.97/1.52  qbf_num_tautologies:                    0
% 7.97/1.52  qbf_prep_cycles:                        0
% 7.97/1.52  
% 7.97/1.52  ------ BMC1
% 7.97/1.52  
% 7.97/1.52  bmc1_current_bound:                     -1
% 7.97/1.52  bmc1_last_solved_bound:                 -1
% 7.97/1.52  bmc1_unsat_core_size:                   -1
% 7.97/1.52  bmc1_unsat_core_parents_size:           -1
% 7.97/1.52  bmc1_merge_next_fun:                    0
% 7.97/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.97/1.52  
% 7.97/1.52  ------ Instantiation
% 7.97/1.52  
% 7.97/1.52  inst_num_of_clauses:                    2883
% 7.97/1.52  inst_num_in_passive:                    1014
% 7.97/1.52  inst_num_in_active:                     1392
% 7.97/1.52  inst_num_in_unprocessed:                477
% 7.97/1.52  inst_num_of_loops:                      1550
% 7.97/1.52  inst_num_of_learning_restarts:          0
% 7.97/1.52  inst_num_moves_active_passive:          155
% 7.97/1.52  inst_lit_activity:                      0
% 7.97/1.52  inst_lit_activity_moves:                1
% 7.97/1.52  inst_num_tautologies:                   0
% 7.97/1.52  inst_num_prop_implied:                  0
% 7.97/1.52  inst_num_existing_simplified:           0
% 7.97/1.52  inst_num_eq_res_simplified:             0
% 7.97/1.52  inst_num_child_elim:                    0
% 7.97/1.52  inst_num_of_dismatching_blockings:      530
% 7.97/1.52  inst_num_of_non_proper_insts:           2442
% 7.97/1.52  inst_num_of_duplicates:                 0
% 7.97/1.52  inst_inst_num_from_inst_to_res:         0
% 7.97/1.52  inst_dismatching_checking_time:         0.
% 7.97/1.52  
% 7.97/1.52  ------ Resolution
% 7.97/1.52  
% 7.97/1.52  res_num_of_clauses:                     0
% 7.97/1.52  res_num_in_passive:                     0
% 7.97/1.52  res_num_in_active:                      0
% 7.97/1.52  res_num_of_loops:                       233
% 7.97/1.52  res_forward_subset_subsumed:            232
% 7.97/1.52  res_backward_subset_subsumed:           0
% 7.97/1.52  res_forward_subsumed:                   0
% 7.97/1.52  res_backward_subsumed:                  0
% 7.97/1.52  res_forward_subsumption_resolution:     2
% 7.97/1.52  res_backward_subsumption_resolution:    0
% 7.97/1.52  res_clause_to_clause_subsumption:       1218
% 7.97/1.52  res_orphan_elimination:                 0
% 7.97/1.52  res_tautology_del:                      70
% 7.97/1.52  res_num_eq_res_simplified:              1
% 7.97/1.52  res_num_sel_changes:                    0
% 7.97/1.52  res_moves_from_active_to_pass:          0
% 7.97/1.52  
% 7.97/1.52  ------ Superposition
% 7.97/1.52  
% 7.97/1.52  sup_time_total:                         0.
% 7.97/1.52  sup_time_generating:                    0.
% 7.97/1.52  sup_time_sim_full:                      0.
% 7.97/1.52  sup_time_sim_immed:                     0.
% 7.97/1.52  
% 7.97/1.52  sup_num_of_clauses:                     562
% 7.97/1.52  sup_num_in_active:                      280
% 7.97/1.52  sup_num_in_passive:                     282
% 7.97/1.52  sup_num_of_loops:                       309
% 7.97/1.52  sup_fw_superposition:                   391
% 7.97/1.52  sup_bw_superposition:                   216
% 7.97/1.52  sup_immediate_simplified:               219
% 7.97/1.52  sup_given_eliminated:                   4
% 7.97/1.52  comparisons_done:                       0
% 7.97/1.52  comparisons_avoided:                    0
% 7.97/1.52  
% 7.97/1.52  ------ Simplifications
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  sim_fw_subset_subsumed:                 4
% 7.97/1.52  sim_bw_subset_subsumed:                 12
% 7.97/1.52  sim_fw_subsumed:                        35
% 7.97/1.52  sim_bw_subsumed:                        1
% 7.97/1.52  sim_fw_subsumption_res:                 0
% 7.97/1.52  sim_bw_subsumption_res:                 0
% 7.97/1.52  sim_tautology_del:                      2
% 7.97/1.52  sim_eq_tautology_del:                   17
% 7.97/1.52  sim_eq_res_simp:                        0
% 7.97/1.52  sim_fw_demodulated:                     26
% 7.97/1.52  sim_bw_demodulated:                     36
% 7.97/1.52  sim_light_normalised:                   196
% 7.97/1.52  sim_joinable_taut:                      0
% 7.97/1.52  sim_joinable_simp:                      0
% 7.97/1.52  sim_ac_normalised:                      0
% 7.97/1.52  sim_smt_subsumption:                    0
% 7.97/1.52  
%------------------------------------------------------------------------------
