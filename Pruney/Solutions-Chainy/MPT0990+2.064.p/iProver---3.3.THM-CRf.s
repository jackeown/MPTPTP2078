%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:10 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  245 (1208 expanded)
%              Number of clauses        :  142 ( 344 expanded)
%              Number of leaves         :   27 ( 312 expanded)
%              Depth                    :   22
%              Number of atoms          :  896 (9795 expanded)
%              Number of equality atoms :  441 (3606 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f66,plain,(
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

fof(f65,plain,
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

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f61,f66,f65])).

fof(f110,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f67])).

fof(f105,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f67])).

fof(f26,axiom,(
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

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f113,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f115,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f67])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f79,f97])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f87,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f123,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f87,f97])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f117,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f97])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f21,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f25,axiom,(
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

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f109,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f114,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

fof(f13,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f82,f97])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f85,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f24,axiom,(
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

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f118,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f76,f97])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f97])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1487,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1500,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2737,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1500])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_2738,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_1500])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1482,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1508,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1511,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5502,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1511])).

cnf(c_12890,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_5502])).

cnf(c_13535,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12890,c_2738])).

cnf(c_13536,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13535])).

cnf(c_13543,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK3),sK3),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_13536])).

cnf(c_41,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1490,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1516,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1515,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2667,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1516,c_1515])).

cnf(c_4228,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1490,c_2667])).

cnf(c_4232,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_4228])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1581,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1676,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_1814,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_4473,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4232,c_47,c_46,c_45,c_41,c_39,c_37,c_1814])).

cnf(c_13549,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13543,c_4473])).

cnf(c_13576,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,sK4)) = k5_relat_1(k6_partfun1(sK2),sK4) ),
    inference(superposition,[status(thm)],[c_2737,c_13549])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1512,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1512,c_4])).

cnf(c_1488,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1506,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4376,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1506])).

cnf(c_48,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_4476,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4376,c_48,c_2738])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k5_relat_1(X2,k6_partfun1(X3)) = X2
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_462,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_1481,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_4478,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4476,c_1481])).

cnf(c_4309,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4310,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4309])).

cnf(c_4697,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top
    | k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4478,c_48,c_2738,c_4310])).

cnf(c_4698,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4697])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1501,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4442,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1501])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1489,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3753,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1489,c_2667])).

cnf(c_3757,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_3753])).

cnf(c_1582,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1702,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1582])).

cnf(c_1827,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_3911,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3757,c_47,c_46,c_45,c_41,c_39,c_37,c_1827])).

cnf(c_4443,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4442,c_3911])).

cnf(c_4644,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4443,c_48,c_2738])).

cnf(c_8,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4656,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4644,c_8])).

cnf(c_4657,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_4656,c_8])).

cnf(c_4703,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
    | m1_subset_1(sK1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4698,c_4657])).

cnf(c_4707,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(sK1)) = k2_funct_1(sK3) ),
    inference(superposition,[status(thm)],[c_1517,c_4703])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_40])).

cnf(c_518,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_27,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_526,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_518,c_27])).

cnf(c_1479,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1760,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2474,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1479,c_47,c_45,c_44,c_42,c_526,c_1760])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_1493,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7434,plain,
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
    inference(demodulation,[status(thm)],[c_1493,c_2667])).

cnf(c_7436,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_7434])).

cnf(c_49,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_7611,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7436,c_48,c_49,c_50])).

cnf(c_7612,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7611])).

cnf(c_7617,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2474,c_7612])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1599,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_848,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1649,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_1936,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK1 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_14,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3540,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3541,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3540])).

cnf(c_7834,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7617,c_51,c_52,c_53,c_38,c_0,c_1599,c_1936,c_3541])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1503,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7839,plain,
    ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7834,c_1503])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_530,plain,
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
    inference(resolution_lifted,[status(thm)],[c_29,c_40])).

cnf(c_531,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_624,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_531])).

cnf(c_1478,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_1975,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1478])).

cnf(c_2481,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1975,c_48,c_49,c_50,c_51,c_52,c_53])).

cnf(c_3758,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2481,c_3753])).

cnf(c_4036,plain,
    ( v2_funct_1(sK4) != iProver_top
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3758,c_51,c_52,c_53,c_38,c_0,c_1599,c_1936])).

cnf(c_4037,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | v2_funct_1(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4036])).

cnf(c_7845,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(superposition,[status(thm)],[c_7834,c_4037])).

cnf(c_7850,plain,
    ( k1_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7839,c_7845])).

cnf(c_9,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_7851,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7850,c_9])).

cnf(c_8789,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7851,c_51,c_2737])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1510,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3417,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK4)),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_2737,c_1510])).

cnf(c_8791,plain,
    ( k5_relat_1(k6_partfun1(sK2),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_8789,c_3417])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1495,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7535,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1495])).

cnf(c_7620,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7535,c_51])).

cnf(c_7621,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7620])).

cnf(c_7629,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_7621])).

cnf(c_7631,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7629,c_2474])).

cnf(c_8936,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7631,c_48])).

cnf(c_13585,plain,
    ( k2_funct_1(sK3) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_13576,c_4707,c_8791,c_8936])).

cnf(c_36,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f116])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13585,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.78/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/1.51  
% 7.78/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.51  
% 7.78/1.51  ------  iProver source info
% 7.78/1.51  
% 7.78/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.51  git: non_committed_changes: false
% 7.78/1.51  git: last_make_outside_of_git: false
% 7.78/1.51  
% 7.78/1.51  ------ 
% 7.78/1.51  
% 7.78/1.51  ------ Input Options
% 7.78/1.51  
% 7.78/1.51  --out_options                           all
% 7.78/1.51  --tptp_safe_out                         true
% 7.78/1.51  --problem_path                          ""
% 7.78/1.51  --include_path                          ""
% 7.78/1.51  --clausifier                            res/vclausify_rel
% 7.78/1.51  --clausifier_options                    ""
% 7.78/1.51  --stdin                                 false
% 7.78/1.51  --stats_out                             all
% 7.78/1.51  
% 7.78/1.51  ------ General Options
% 7.78/1.51  
% 7.78/1.51  --fof                                   false
% 7.78/1.51  --time_out_real                         305.
% 7.78/1.51  --time_out_virtual                      -1.
% 7.78/1.51  --symbol_type_check                     false
% 7.78/1.51  --clausify_out                          false
% 7.78/1.51  --sig_cnt_out                           false
% 7.78/1.51  --trig_cnt_out                          false
% 7.78/1.51  --trig_cnt_out_tolerance                1.
% 7.78/1.51  --trig_cnt_out_sk_spl                   false
% 7.78/1.51  --abstr_cl_out                          false
% 7.78/1.51  
% 7.78/1.51  ------ Global Options
% 7.78/1.51  
% 7.78/1.51  --schedule                              default
% 7.78/1.51  --add_important_lit                     false
% 7.78/1.51  --prop_solver_per_cl                    1000
% 7.78/1.51  --min_unsat_core                        false
% 7.78/1.51  --soft_assumptions                      false
% 7.78/1.51  --soft_lemma_size                       3
% 7.78/1.51  --prop_impl_unit_size                   0
% 7.78/1.51  --prop_impl_unit                        []
% 7.78/1.51  --share_sel_clauses                     true
% 7.78/1.51  --reset_solvers                         false
% 7.78/1.51  --bc_imp_inh                            [conj_cone]
% 7.78/1.51  --conj_cone_tolerance                   3.
% 7.78/1.51  --extra_neg_conj                        none
% 7.78/1.51  --large_theory_mode                     true
% 7.78/1.51  --prolific_symb_bound                   200
% 7.78/1.51  --lt_threshold                          2000
% 7.78/1.51  --clause_weak_htbl                      true
% 7.78/1.51  --gc_record_bc_elim                     false
% 7.78/1.51  
% 7.78/1.51  ------ Preprocessing Options
% 7.78/1.51  
% 7.78/1.51  --preprocessing_flag                    true
% 7.78/1.51  --time_out_prep_mult                    0.1
% 7.78/1.51  --splitting_mode                        input
% 7.78/1.51  --splitting_grd                         true
% 7.78/1.51  --splitting_cvd                         false
% 7.78/1.51  --splitting_cvd_svl                     false
% 7.78/1.51  --splitting_nvd                         32
% 7.78/1.51  --sub_typing                            true
% 7.78/1.51  --prep_gs_sim                           true
% 7.78/1.51  --prep_unflatten                        true
% 7.78/1.51  --prep_res_sim                          true
% 7.78/1.51  --prep_upred                            true
% 7.78/1.51  --prep_sem_filter                       exhaustive
% 7.78/1.51  --prep_sem_filter_out                   false
% 7.78/1.51  --pred_elim                             true
% 7.78/1.51  --res_sim_input                         true
% 7.78/1.51  --eq_ax_congr_red                       true
% 7.78/1.51  --pure_diseq_elim                       true
% 7.78/1.51  --brand_transform                       false
% 7.78/1.51  --non_eq_to_eq                          false
% 7.78/1.51  --prep_def_merge                        true
% 7.78/1.51  --prep_def_merge_prop_impl              false
% 7.78/1.51  --prep_def_merge_mbd                    true
% 7.78/1.51  --prep_def_merge_tr_red                 false
% 7.78/1.51  --prep_def_merge_tr_cl                  false
% 7.78/1.51  --smt_preprocessing                     true
% 7.78/1.51  --smt_ac_axioms                         fast
% 7.78/1.51  --preprocessed_out                      false
% 7.78/1.51  --preprocessed_stats                    false
% 7.78/1.51  
% 7.78/1.51  ------ Abstraction refinement Options
% 7.78/1.51  
% 7.78/1.51  --abstr_ref                             []
% 7.78/1.51  --abstr_ref_prep                        false
% 7.78/1.51  --abstr_ref_until_sat                   false
% 7.78/1.51  --abstr_ref_sig_restrict                funpre
% 7.78/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.51  --abstr_ref_under                       []
% 7.78/1.51  
% 7.78/1.51  ------ SAT Options
% 7.78/1.51  
% 7.78/1.51  --sat_mode                              false
% 7.78/1.51  --sat_fm_restart_options                ""
% 7.78/1.51  --sat_gr_def                            false
% 7.78/1.51  --sat_epr_types                         true
% 7.78/1.51  --sat_non_cyclic_types                  false
% 7.78/1.51  --sat_finite_models                     false
% 7.78/1.51  --sat_fm_lemmas                         false
% 7.78/1.51  --sat_fm_prep                           false
% 7.78/1.51  --sat_fm_uc_incr                        true
% 7.78/1.51  --sat_out_model                         small
% 7.78/1.51  --sat_out_clauses                       false
% 7.78/1.51  
% 7.78/1.51  ------ QBF Options
% 7.78/1.51  
% 7.78/1.51  --qbf_mode                              false
% 7.78/1.51  --qbf_elim_univ                         false
% 7.78/1.51  --qbf_dom_inst                          none
% 7.78/1.51  --qbf_dom_pre_inst                      false
% 7.78/1.51  --qbf_sk_in                             false
% 7.78/1.51  --qbf_pred_elim                         true
% 7.78/1.51  --qbf_split                             512
% 7.78/1.51  
% 7.78/1.51  ------ BMC1 Options
% 7.78/1.51  
% 7.78/1.51  --bmc1_incremental                      false
% 7.78/1.51  --bmc1_axioms                           reachable_all
% 7.78/1.51  --bmc1_min_bound                        0
% 7.78/1.51  --bmc1_max_bound                        -1
% 7.78/1.51  --bmc1_max_bound_default                -1
% 7.78/1.51  --bmc1_symbol_reachability              true
% 7.78/1.51  --bmc1_property_lemmas                  false
% 7.78/1.51  --bmc1_k_induction                      false
% 7.78/1.51  --bmc1_non_equiv_states                 false
% 7.78/1.51  --bmc1_deadlock                         false
% 7.78/1.51  --bmc1_ucm                              false
% 7.78/1.51  --bmc1_add_unsat_core                   none
% 7.78/1.51  --bmc1_unsat_core_children              false
% 7.78/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.51  --bmc1_out_stat                         full
% 7.78/1.51  --bmc1_ground_init                      false
% 7.78/1.51  --bmc1_pre_inst_next_state              false
% 7.78/1.51  --bmc1_pre_inst_state                   false
% 7.78/1.51  --bmc1_pre_inst_reach_state             false
% 7.78/1.51  --bmc1_out_unsat_core                   false
% 7.78/1.51  --bmc1_aig_witness_out                  false
% 7.78/1.51  --bmc1_verbose                          false
% 7.78/1.51  --bmc1_dump_clauses_tptp                false
% 7.78/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.51  --bmc1_dump_file                        -
% 7.78/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.51  --bmc1_ucm_extend_mode                  1
% 7.78/1.51  --bmc1_ucm_init_mode                    2
% 7.78/1.51  --bmc1_ucm_cone_mode                    none
% 7.78/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.51  --bmc1_ucm_relax_model                  4
% 7.78/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.51  --bmc1_ucm_layered_model                none
% 7.78/1.51  --bmc1_ucm_max_lemma_size               10
% 7.78/1.51  
% 7.78/1.51  ------ AIG Options
% 7.78/1.51  
% 7.78/1.51  --aig_mode                              false
% 7.78/1.51  
% 7.78/1.51  ------ Instantiation Options
% 7.78/1.51  
% 7.78/1.51  --instantiation_flag                    true
% 7.78/1.51  --inst_sos_flag                         true
% 7.78/1.51  --inst_sos_phase                        true
% 7.78/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.51  --inst_lit_sel_side                     num_symb
% 7.78/1.51  --inst_solver_per_active                1400
% 7.78/1.51  --inst_solver_calls_frac                1.
% 7.78/1.51  --inst_passive_queue_type               priority_queues
% 7.78/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.51  --inst_passive_queues_freq              [25;2]
% 7.78/1.51  --inst_dismatching                      true
% 7.78/1.51  --inst_eager_unprocessed_to_passive     true
% 7.78/1.51  --inst_prop_sim_given                   true
% 7.78/1.51  --inst_prop_sim_new                     false
% 7.78/1.51  --inst_subs_new                         false
% 7.78/1.51  --inst_eq_res_simp                      false
% 7.78/1.51  --inst_subs_given                       false
% 7.78/1.51  --inst_orphan_elimination               true
% 7.78/1.51  --inst_learning_loop_flag               true
% 7.78/1.51  --inst_learning_start                   3000
% 7.78/1.51  --inst_learning_factor                  2
% 7.78/1.51  --inst_start_prop_sim_after_learn       3
% 7.78/1.51  --inst_sel_renew                        solver
% 7.78/1.51  --inst_lit_activity_flag                true
% 7.78/1.51  --inst_restr_to_given                   false
% 7.78/1.51  --inst_activity_threshold               500
% 7.78/1.51  --inst_out_proof                        true
% 7.78/1.51  
% 7.78/1.51  ------ Resolution Options
% 7.78/1.51  
% 7.78/1.51  --resolution_flag                       true
% 7.78/1.51  --res_lit_sel                           adaptive
% 7.78/1.51  --res_lit_sel_side                      none
% 7.78/1.51  --res_ordering                          kbo
% 7.78/1.51  --res_to_prop_solver                    active
% 7.78/1.51  --res_prop_simpl_new                    false
% 7.78/1.51  --res_prop_simpl_given                  true
% 7.78/1.51  --res_passive_queue_type                priority_queues
% 7.78/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.51  --res_passive_queues_freq               [15;5]
% 7.78/1.51  --res_forward_subs                      full
% 7.78/1.51  --res_backward_subs                     full
% 7.78/1.51  --res_forward_subs_resolution           true
% 7.78/1.51  --res_backward_subs_resolution          true
% 7.78/1.51  --res_orphan_elimination                true
% 7.78/1.51  --res_time_limit                        2.
% 7.78/1.51  --res_out_proof                         true
% 7.78/1.51  
% 7.78/1.51  ------ Superposition Options
% 7.78/1.51  
% 7.78/1.51  --superposition_flag                    true
% 7.78/1.51  --sup_passive_queue_type                priority_queues
% 7.78/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.51  --demod_completeness_check              fast
% 7.78/1.51  --demod_use_ground                      true
% 7.78/1.51  --sup_to_prop_solver                    passive
% 7.78/1.51  --sup_prop_simpl_new                    true
% 7.78/1.51  --sup_prop_simpl_given                  true
% 7.78/1.51  --sup_fun_splitting                     true
% 7.78/1.51  --sup_smt_interval                      50000
% 7.78/1.51  
% 7.78/1.51  ------ Superposition Simplification Setup
% 7.78/1.51  
% 7.78/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.51  --sup_immed_triv                        [TrivRules]
% 7.78/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.51  --sup_immed_bw_main                     []
% 7.78/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.51  --sup_input_bw                          []
% 7.78/1.51  
% 7.78/1.51  ------ Combination Options
% 7.78/1.51  
% 7.78/1.51  --comb_res_mult                         3
% 7.78/1.51  --comb_sup_mult                         2
% 7.78/1.51  --comb_inst_mult                        10
% 7.78/1.51  
% 7.78/1.51  ------ Debug Options
% 7.78/1.51  
% 7.78/1.51  --dbg_backtrace                         false
% 7.78/1.51  --dbg_dump_prop_clauses                 false
% 7.78/1.51  --dbg_dump_prop_clauses_file            -
% 7.78/1.51  --dbg_out_stat                          false
% 7.78/1.51  ------ Parsing...
% 7.78/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.51  
% 7.78/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.78/1.51  
% 7.78/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.51  
% 7.78/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.51  ------ Proving...
% 7.78/1.51  ------ Problem Properties 
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  clauses                                 46
% 7.78/1.51  conjectures                             11
% 7.78/1.51  EPR                                     11
% 7.78/1.51  Horn                                    42
% 7.78/1.51  unary                                   19
% 7.78/1.51  binary                                  5
% 7.78/1.51  lits                                    152
% 7.78/1.51  lits eq                                 37
% 7.78/1.51  fd_pure                                 0
% 7.78/1.51  fd_pseudo                               0
% 7.78/1.51  fd_cond                                 5
% 7.78/1.51  fd_pseudo_cond                          1
% 7.78/1.51  AC symbols                              0
% 7.78/1.51  
% 7.78/1.51  ------ Schedule dynamic 5 is on 
% 7.78/1.51  
% 7.78/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  ------ 
% 7.78/1.51  Current options:
% 7.78/1.51  ------ 
% 7.78/1.51  
% 7.78/1.51  ------ Input Options
% 7.78/1.51  
% 7.78/1.51  --out_options                           all
% 7.78/1.51  --tptp_safe_out                         true
% 7.78/1.51  --problem_path                          ""
% 7.78/1.51  --include_path                          ""
% 7.78/1.51  --clausifier                            res/vclausify_rel
% 7.78/1.51  --clausifier_options                    ""
% 7.78/1.51  --stdin                                 false
% 7.78/1.51  --stats_out                             all
% 7.78/1.51  
% 7.78/1.51  ------ General Options
% 7.78/1.51  
% 7.78/1.51  --fof                                   false
% 7.78/1.51  --time_out_real                         305.
% 7.78/1.51  --time_out_virtual                      -1.
% 7.78/1.51  --symbol_type_check                     false
% 7.78/1.51  --clausify_out                          false
% 7.78/1.51  --sig_cnt_out                           false
% 7.78/1.51  --trig_cnt_out                          false
% 7.78/1.51  --trig_cnt_out_tolerance                1.
% 7.78/1.51  --trig_cnt_out_sk_spl                   false
% 7.78/1.51  --abstr_cl_out                          false
% 7.78/1.51  
% 7.78/1.51  ------ Global Options
% 7.78/1.51  
% 7.78/1.51  --schedule                              default
% 7.78/1.51  --add_important_lit                     false
% 7.78/1.51  --prop_solver_per_cl                    1000
% 7.78/1.51  --min_unsat_core                        false
% 7.78/1.51  --soft_assumptions                      false
% 7.78/1.51  --soft_lemma_size                       3
% 7.78/1.51  --prop_impl_unit_size                   0
% 7.78/1.51  --prop_impl_unit                        []
% 7.78/1.51  --share_sel_clauses                     true
% 7.78/1.51  --reset_solvers                         false
% 7.78/1.51  --bc_imp_inh                            [conj_cone]
% 7.78/1.51  --conj_cone_tolerance                   3.
% 7.78/1.51  --extra_neg_conj                        none
% 7.78/1.51  --large_theory_mode                     true
% 7.78/1.51  --prolific_symb_bound                   200
% 7.78/1.51  --lt_threshold                          2000
% 7.78/1.51  --clause_weak_htbl                      true
% 7.78/1.51  --gc_record_bc_elim                     false
% 7.78/1.51  
% 7.78/1.51  ------ Preprocessing Options
% 7.78/1.51  
% 7.78/1.51  --preprocessing_flag                    true
% 7.78/1.51  --time_out_prep_mult                    0.1
% 7.78/1.51  --splitting_mode                        input
% 7.78/1.51  --splitting_grd                         true
% 7.78/1.51  --splitting_cvd                         false
% 7.78/1.51  --splitting_cvd_svl                     false
% 7.78/1.51  --splitting_nvd                         32
% 7.78/1.51  --sub_typing                            true
% 7.78/1.51  --prep_gs_sim                           true
% 7.78/1.51  --prep_unflatten                        true
% 7.78/1.51  --prep_res_sim                          true
% 7.78/1.51  --prep_upred                            true
% 7.78/1.51  --prep_sem_filter                       exhaustive
% 7.78/1.51  --prep_sem_filter_out                   false
% 7.78/1.51  --pred_elim                             true
% 7.78/1.51  --res_sim_input                         true
% 7.78/1.51  --eq_ax_congr_red                       true
% 7.78/1.51  --pure_diseq_elim                       true
% 7.78/1.51  --brand_transform                       false
% 7.78/1.51  --non_eq_to_eq                          false
% 7.78/1.51  --prep_def_merge                        true
% 7.78/1.51  --prep_def_merge_prop_impl              false
% 7.78/1.51  --prep_def_merge_mbd                    true
% 7.78/1.51  --prep_def_merge_tr_red                 false
% 7.78/1.51  --prep_def_merge_tr_cl                  false
% 7.78/1.51  --smt_preprocessing                     true
% 7.78/1.51  --smt_ac_axioms                         fast
% 7.78/1.51  --preprocessed_out                      false
% 7.78/1.51  --preprocessed_stats                    false
% 7.78/1.51  
% 7.78/1.51  ------ Abstraction refinement Options
% 7.78/1.51  
% 7.78/1.51  --abstr_ref                             []
% 7.78/1.51  --abstr_ref_prep                        false
% 7.78/1.51  --abstr_ref_until_sat                   false
% 7.78/1.51  --abstr_ref_sig_restrict                funpre
% 7.78/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.51  --abstr_ref_under                       []
% 7.78/1.51  
% 7.78/1.51  ------ SAT Options
% 7.78/1.51  
% 7.78/1.51  --sat_mode                              false
% 7.78/1.51  --sat_fm_restart_options                ""
% 7.78/1.51  --sat_gr_def                            false
% 7.78/1.51  --sat_epr_types                         true
% 7.78/1.51  --sat_non_cyclic_types                  false
% 7.78/1.51  --sat_finite_models                     false
% 7.78/1.51  --sat_fm_lemmas                         false
% 7.78/1.51  --sat_fm_prep                           false
% 7.78/1.51  --sat_fm_uc_incr                        true
% 7.78/1.51  --sat_out_model                         small
% 7.78/1.51  --sat_out_clauses                       false
% 7.78/1.51  
% 7.78/1.51  ------ QBF Options
% 7.78/1.51  
% 7.78/1.51  --qbf_mode                              false
% 7.78/1.51  --qbf_elim_univ                         false
% 7.78/1.51  --qbf_dom_inst                          none
% 7.78/1.51  --qbf_dom_pre_inst                      false
% 7.78/1.51  --qbf_sk_in                             false
% 7.78/1.51  --qbf_pred_elim                         true
% 7.78/1.51  --qbf_split                             512
% 7.78/1.51  
% 7.78/1.51  ------ BMC1 Options
% 7.78/1.51  
% 7.78/1.51  --bmc1_incremental                      false
% 7.78/1.51  --bmc1_axioms                           reachable_all
% 7.78/1.51  --bmc1_min_bound                        0
% 7.78/1.51  --bmc1_max_bound                        -1
% 7.78/1.51  --bmc1_max_bound_default                -1
% 7.78/1.51  --bmc1_symbol_reachability              true
% 7.78/1.51  --bmc1_property_lemmas                  false
% 7.78/1.51  --bmc1_k_induction                      false
% 7.78/1.51  --bmc1_non_equiv_states                 false
% 7.78/1.51  --bmc1_deadlock                         false
% 7.78/1.51  --bmc1_ucm                              false
% 7.78/1.51  --bmc1_add_unsat_core                   none
% 7.78/1.51  --bmc1_unsat_core_children              false
% 7.78/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.51  --bmc1_out_stat                         full
% 7.78/1.51  --bmc1_ground_init                      false
% 7.78/1.51  --bmc1_pre_inst_next_state              false
% 7.78/1.51  --bmc1_pre_inst_state                   false
% 7.78/1.51  --bmc1_pre_inst_reach_state             false
% 7.78/1.51  --bmc1_out_unsat_core                   false
% 7.78/1.51  --bmc1_aig_witness_out                  false
% 7.78/1.51  --bmc1_verbose                          false
% 7.78/1.51  --bmc1_dump_clauses_tptp                false
% 7.78/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.51  --bmc1_dump_file                        -
% 7.78/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.51  --bmc1_ucm_extend_mode                  1
% 7.78/1.51  --bmc1_ucm_init_mode                    2
% 7.78/1.51  --bmc1_ucm_cone_mode                    none
% 7.78/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.51  --bmc1_ucm_relax_model                  4
% 7.78/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.51  --bmc1_ucm_layered_model                none
% 7.78/1.51  --bmc1_ucm_max_lemma_size               10
% 7.78/1.51  
% 7.78/1.51  ------ AIG Options
% 7.78/1.51  
% 7.78/1.51  --aig_mode                              false
% 7.78/1.51  
% 7.78/1.51  ------ Instantiation Options
% 7.78/1.51  
% 7.78/1.51  --instantiation_flag                    true
% 7.78/1.51  --inst_sos_flag                         true
% 7.78/1.51  --inst_sos_phase                        true
% 7.78/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.51  --inst_lit_sel_side                     none
% 7.78/1.51  --inst_solver_per_active                1400
% 7.78/1.51  --inst_solver_calls_frac                1.
% 7.78/1.51  --inst_passive_queue_type               priority_queues
% 7.78/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.51  --inst_passive_queues_freq              [25;2]
% 7.78/1.51  --inst_dismatching                      true
% 7.78/1.51  --inst_eager_unprocessed_to_passive     true
% 7.78/1.51  --inst_prop_sim_given                   true
% 7.78/1.51  --inst_prop_sim_new                     false
% 7.78/1.51  --inst_subs_new                         false
% 7.78/1.51  --inst_eq_res_simp                      false
% 7.78/1.51  --inst_subs_given                       false
% 7.78/1.51  --inst_orphan_elimination               true
% 7.78/1.51  --inst_learning_loop_flag               true
% 7.78/1.51  --inst_learning_start                   3000
% 7.78/1.51  --inst_learning_factor                  2
% 7.78/1.51  --inst_start_prop_sim_after_learn       3
% 7.78/1.51  --inst_sel_renew                        solver
% 7.78/1.51  --inst_lit_activity_flag                true
% 7.78/1.51  --inst_restr_to_given                   false
% 7.78/1.51  --inst_activity_threshold               500
% 7.78/1.51  --inst_out_proof                        true
% 7.78/1.51  
% 7.78/1.51  ------ Resolution Options
% 7.78/1.51  
% 7.78/1.51  --resolution_flag                       false
% 7.78/1.51  --res_lit_sel                           adaptive
% 7.78/1.51  --res_lit_sel_side                      none
% 7.78/1.51  --res_ordering                          kbo
% 7.78/1.51  --res_to_prop_solver                    active
% 7.78/1.51  --res_prop_simpl_new                    false
% 7.78/1.51  --res_prop_simpl_given                  true
% 7.78/1.51  --res_passive_queue_type                priority_queues
% 7.78/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.51  --res_passive_queues_freq               [15;5]
% 7.78/1.51  --res_forward_subs                      full
% 7.78/1.51  --res_backward_subs                     full
% 7.78/1.51  --res_forward_subs_resolution           true
% 7.78/1.51  --res_backward_subs_resolution          true
% 7.78/1.51  --res_orphan_elimination                true
% 7.78/1.51  --res_time_limit                        2.
% 7.78/1.51  --res_out_proof                         true
% 7.78/1.51  
% 7.78/1.51  ------ Superposition Options
% 7.78/1.51  
% 7.78/1.51  --superposition_flag                    true
% 7.78/1.51  --sup_passive_queue_type                priority_queues
% 7.78/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.51  --demod_completeness_check              fast
% 7.78/1.51  --demod_use_ground                      true
% 7.78/1.51  --sup_to_prop_solver                    passive
% 7.78/1.51  --sup_prop_simpl_new                    true
% 7.78/1.51  --sup_prop_simpl_given                  true
% 7.78/1.51  --sup_fun_splitting                     true
% 7.78/1.51  --sup_smt_interval                      50000
% 7.78/1.51  
% 7.78/1.51  ------ Superposition Simplification Setup
% 7.78/1.51  
% 7.78/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.51  --sup_immed_triv                        [TrivRules]
% 7.78/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.51  --sup_immed_bw_main                     []
% 7.78/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.51  --sup_input_bw                          []
% 7.78/1.51  
% 7.78/1.51  ------ Combination Options
% 7.78/1.51  
% 7.78/1.51  --comb_res_mult                         3
% 7.78/1.51  --comb_sup_mult                         2
% 7.78/1.51  --comb_inst_mult                        10
% 7.78/1.51  
% 7.78/1.51  ------ Debug Options
% 7.78/1.51  
% 7.78/1.51  --dbg_backtrace                         false
% 7.78/1.51  --dbg_dump_prop_clauses                 false
% 7.78/1.51  --dbg_dump_prop_clauses_file            -
% 7.78/1.51  --dbg_out_stat                          false
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  ------ Proving...
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  % SZS status Theorem for theBenchmark.p
% 7.78/1.51  
% 7.78/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.51  
% 7.78/1.51  fof(f27,conjecture,(
% 7.78/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f28,negated_conjecture,(
% 7.78/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.78/1.51    inference(negated_conjecture,[],[f27])).
% 7.78/1.51  
% 7.78/1.51  fof(f60,plain,(
% 7.78/1.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.78/1.51    inference(ennf_transformation,[],[f28])).
% 7.78/1.51  
% 7.78/1.51  fof(f61,plain,(
% 7.78/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.78/1.51    inference(flattening,[],[f60])).
% 7.78/1.51  
% 7.78/1.51  fof(f66,plain,(
% 7.78/1.51    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 7.78/1.51    introduced(choice_axiom,[])).
% 7.78/1.51  
% 7.78/1.51  fof(f65,plain,(
% 7.78/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.78/1.51    introduced(choice_axiom,[])).
% 7.78/1.51  
% 7.78/1.51  fof(f67,plain,(
% 7.78/1.51    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.78/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f61,f66,f65])).
% 7.78/1.51  
% 7.78/1.51  fof(f110,plain,(
% 7.78/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f17,axiom,(
% 7.78/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f46,plain,(
% 7.78/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.78/1.51    inference(ennf_transformation,[],[f17])).
% 7.78/1.51  
% 7.78/1.51  fof(f89,plain,(
% 7.78/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.78/1.51    inference(cnf_transformation,[],[f46])).
% 7.78/1.51  
% 7.78/1.51  fof(f107,plain,(
% 7.78/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f105,plain,(
% 7.78/1.51    v1_funct_1(sK3)),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f12,axiom,(
% 7.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f38,plain,(
% 7.78/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.78/1.51    inference(ennf_transformation,[],[f12])).
% 7.78/1.51  
% 7.78/1.51  fof(f39,plain,(
% 7.78/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.78/1.51    inference(flattening,[],[f38])).
% 7.78/1.51  
% 7.78/1.51  fof(f80,plain,(
% 7.78/1.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f39])).
% 7.78/1.51  
% 7.78/1.51  fof(f8,axiom,(
% 7.78/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f34,plain,(
% 7.78/1.51    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.78/1.51    inference(ennf_transformation,[],[f8])).
% 7.78/1.51  
% 7.78/1.51  fof(f75,plain,(
% 7.78/1.51    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f34])).
% 7.78/1.51  
% 7.78/1.51  fof(f111,plain,(
% 7.78/1.51    k2_relset_1(sK1,sK2,sK3) = sK2),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f26,axiom,(
% 7.78/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f58,plain,(
% 7.78/1.51    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.78/1.51    inference(ennf_transformation,[],[f26])).
% 7.78/1.51  
% 7.78/1.51  fof(f59,plain,(
% 7.78/1.51    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.78/1.51    inference(flattening,[],[f58])).
% 7.78/1.51  
% 7.78/1.51  fof(f104,plain,(
% 7.78/1.51    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f59])).
% 7.78/1.51  
% 7.78/1.51  fof(f1,axiom,(
% 7.78/1.51    v1_xboole_0(o_0_0_xboole_0)),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f68,plain,(
% 7.78/1.51    v1_xboole_0(o_0_0_xboole_0)),
% 7.78/1.51    inference(cnf_transformation,[],[f1])).
% 7.78/1.51  
% 7.78/1.51  fof(f2,axiom,(
% 7.78/1.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f31,plain,(
% 7.78/1.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.78/1.51    inference(ennf_transformation,[],[f2])).
% 7.78/1.51  
% 7.78/1.51  fof(f69,plain,(
% 7.78/1.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f31])).
% 7.78/1.51  
% 7.78/1.51  fof(f106,plain,(
% 7.78/1.51    v1_funct_2(sK3,sK1,sK2)),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f113,plain,(
% 7.78/1.51    v2_funct_1(sK3)),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f115,plain,(
% 7.78/1.51    k1_xboole_0 != sK2),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f6,axiom,(
% 7.78/1.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f73,plain,(
% 7.78/1.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.78/1.51    inference(cnf_transformation,[],[f6])).
% 7.78/1.51  
% 7.78/1.51  fof(f5,axiom,(
% 7.78/1.51    ! [X0] : k2_subset_1(X0) = X0),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f72,plain,(
% 7.78/1.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.78/1.51    inference(cnf_transformation,[],[f5])).
% 7.78/1.51  
% 7.78/1.51  fof(f14,axiom,(
% 7.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f40,plain,(
% 7.78/1.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.78/1.51    inference(ennf_transformation,[],[f14])).
% 7.78/1.51  
% 7.78/1.51  fof(f41,plain,(
% 7.78/1.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.78/1.51    inference(flattening,[],[f40])).
% 7.78/1.51  
% 7.78/1.51  fof(f84,plain,(
% 7.78/1.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f41])).
% 7.78/1.51  
% 7.78/1.51  fof(f7,axiom,(
% 7.78/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f29,plain,(
% 7.78/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 7.78/1.51    inference(unused_predicate_definition_removal,[],[f7])).
% 7.78/1.51  
% 7.78/1.51  fof(f33,plain,(
% 7.78/1.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.78/1.51    inference(ennf_transformation,[],[f29])).
% 7.78/1.51  
% 7.78/1.51  fof(f74,plain,(
% 7.78/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.78/1.51    inference(cnf_transformation,[],[f33])).
% 7.78/1.51  
% 7.78/1.51  fof(f11,axiom,(
% 7.78/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f36,plain,(
% 7.78/1.51    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.78/1.51    inference(ennf_transformation,[],[f11])).
% 7.78/1.51  
% 7.78/1.51  fof(f37,plain,(
% 7.78/1.51    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.78/1.51    inference(flattening,[],[f36])).
% 7.78/1.51  
% 7.78/1.51  fof(f79,plain,(
% 7.78/1.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f37])).
% 7.78/1.51  
% 7.78/1.51  fof(f23,axiom,(
% 7.78/1.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f97,plain,(
% 7.78/1.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f23])).
% 7.78/1.51  
% 7.78/1.51  fof(f120,plain,(
% 7.78/1.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.78/1.51    inference(definition_unfolding,[],[f79,f97])).
% 7.78/1.51  
% 7.78/1.51  fof(f16,axiom,(
% 7.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f44,plain,(
% 7.78/1.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.78/1.51    inference(ennf_transformation,[],[f16])).
% 7.78/1.51  
% 7.78/1.51  fof(f45,plain,(
% 7.78/1.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.78/1.51    inference(flattening,[],[f44])).
% 7.78/1.51  
% 7.78/1.51  fof(f87,plain,(
% 7.78/1.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f45])).
% 7.78/1.51  
% 7.78/1.51  fof(f123,plain,(
% 7.78/1.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(definition_unfolding,[],[f87,f97])).
% 7.78/1.51  
% 7.78/1.51  fof(f103,plain,(
% 7.78/1.51    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f59])).
% 7.78/1.51  
% 7.78/1.51  fof(f9,axiom,(
% 7.78/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f77,plain,(
% 7.78/1.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.78/1.51    inference(cnf_transformation,[],[f9])).
% 7.78/1.51  
% 7.78/1.51  fof(f117,plain,(
% 7.78/1.51    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.78/1.51    inference(definition_unfolding,[],[f77,f97])).
% 7.78/1.51  
% 7.78/1.51  fof(f19,axiom,(
% 7.78/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f48,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.78/1.51    inference(ennf_transformation,[],[f19])).
% 7.78/1.51  
% 7.78/1.51  fof(f49,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.78/1.51    inference(flattening,[],[f48])).
% 7.78/1.51  
% 7.78/1.51  fof(f64,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.78/1.51    inference(nnf_transformation,[],[f49])).
% 7.78/1.51  
% 7.78/1.51  fof(f91,plain,(
% 7.78/1.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.78/1.51    inference(cnf_transformation,[],[f64])).
% 7.78/1.51  
% 7.78/1.51  fof(f112,plain,(
% 7.78/1.51    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f21,axiom,(
% 7.78/1.51    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f30,plain,(
% 7.78/1.51    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.78/1.51    inference(pure_predicate_removal,[],[f21])).
% 7.78/1.51  
% 7.78/1.51  fof(f95,plain,(
% 7.78/1.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.78/1.51    inference(cnf_transformation,[],[f30])).
% 7.78/1.51  
% 7.78/1.51  fof(f108,plain,(
% 7.78/1.51    v1_funct_1(sK4)),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f20,axiom,(
% 7.78/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f50,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.78/1.51    inference(ennf_transformation,[],[f20])).
% 7.78/1.51  
% 7.78/1.51  fof(f51,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.78/1.51    inference(flattening,[],[f50])).
% 7.78/1.51  
% 7.78/1.51  fof(f94,plain,(
% 7.78/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f51])).
% 7.78/1.51  
% 7.78/1.51  fof(f25,axiom,(
% 7.78/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f56,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.78/1.51    inference(ennf_transformation,[],[f25])).
% 7.78/1.51  
% 7.78/1.51  fof(f57,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.78/1.51    inference(flattening,[],[f56])).
% 7.78/1.51  
% 7.78/1.51  fof(f101,plain,(
% 7.78/1.51    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f57])).
% 7.78/1.51  
% 7.78/1.51  fof(f109,plain,(
% 7.78/1.51    v1_funct_2(sK4,sK2,sK1)),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f114,plain,(
% 7.78/1.51    k1_xboole_0 != sK1),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  fof(f13,axiom,(
% 7.78/1.51    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f82,plain,(
% 7.78/1.51    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.78/1.51    inference(cnf_transformation,[],[f13])).
% 7.78/1.51  
% 7.78/1.51  fof(f121,plain,(
% 7.78/1.51    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.78/1.51    inference(definition_unfolding,[],[f82,f97])).
% 7.78/1.51  
% 7.78/1.51  fof(f15,axiom,(
% 7.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f42,plain,(
% 7.78/1.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.78/1.51    inference(ennf_transformation,[],[f15])).
% 7.78/1.51  
% 7.78/1.51  fof(f43,plain,(
% 7.78/1.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.78/1.51    inference(flattening,[],[f42])).
% 7.78/1.51  
% 7.78/1.51  fof(f85,plain,(
% 7.78/1.51    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f43])).
% 7.78/1.51  
% 7.78/1.51  fof(f24,axiom,(
% 7.78/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f54,plain,(
% 7.78/1.51    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.78/1.51    inference(ennf_transformation,[],[f24])).
% 7.78/1.51  
% 7.78/1.51  fof(f55,plain,(
% 7.78/1.51    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.78/1.51    inference(flattening,[],[f54])).
% 7.78/1.51  
% 7.78/1.51  fof(f98,plain,(
% 7.78/1.51    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f55])).
% 7.78/1.51  
% 7.78/1.51  fof(f76,plain,(
% 7.78/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.78/1.51    inference(cnf_transformation,[],[f9])).
% 7.78/1.51  
% 7.78/1.51  fof(f118,plain,(
% 7.78/1.51    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.78/1.51    inference(definition_unfolding,[],[f76,f97])).
% 7.78/1.51  
% 7.78/1.51  fof(f10,axiom,(
% 7.78/1.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f35,plain,(
% 7.78/1.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.78/1.51    inference(ennf_transformation,[],[f10])).
% 7.78/1.51  
% 7.78/1.51  fof(f78,plain,(
% 7.78/1.51    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f35])).
% 7.78/1.51  
% 7.78/1.51  fof(f119,plain,(
% 7.78/1.51    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.78/1.51    inference(definition_unfolding,[],[f78,f97])).
% 7.78/1.51  
% 7.78/1.51  fof(f22,axiom,(
% 7.78/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.78/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.51  
% 7.78/1.51  fof(f52,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.78/1.51    inference(ennf_transformation,[],[f22])).
% 7.78/1.51  
% 7.78/1.51  fof(f53,plain,(
% 7.78/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.78/1.51    inference(flattening,[],[f52])).
% 7.78/1.51  
% 7.78/1.51  fof(f96,plain,(
% 7.78/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.78/1.51    inference(cnf_transformation,[],[f53])).
% 7.78/1.51  
% 7.78/1.51  fof(f116,plain,(
% 7.78/1.51    k2_funct_1(sK3) != sK4),
% 7.78/1.51    inference(cnf_transformation,[],[f67])).
% 7.78/1.51  
% 7.78/1.51  cnf(c_42,negated_conjecture,
% 7.78/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.78/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1487,plain,
% 7.78/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_21,plain,
% 7.78/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | v1_relat_1(X0) ),
% 7.78/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1500,plain,
% 7.78/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_2737,plain,
% 7.78/1.51      ( v1_relat_1(sK4) = iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1487,c_1500]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_45,negated_conjecture,
% 7.78/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.78/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1484,plain,
% 7.78/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_2738,plain,
% 7.78/1.51      ( v1_relat_1(sK3) = iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1484,c_1500]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_47,negated_conjecture,
% 7.78/1.51      ( v1_funct_1(sK3) ),
% 7.78/1.51      inference(cnf_transformation,[],[f105]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1482,plain,
% 7.78/1.51      ( v1_funct_1(sK3) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_13,plain,
% 7.78/1.51      ( ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_relat_1(X0)
% 7.78/1.51      | v1_relat_1(k2_funct_1(X0)) ),
% 7.78/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1508,plain,
% 7.78/1.51      ( v1_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7,plain,
% 7.78/1.51      ( ~ v1_relat_1(X0)
% 7.78/1.51      | ~ v1_relat_1(X1)
% 7.78/1.51      | ~ v1_relat_1(X2)
% 7.78/1.51      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 7.78/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1511,plain,
% 7.78/1.51      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.78/1.51      | v1_relat_1(X2) != iProver_top
% 7.78/1.51      | v1_relat_1(X1) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_5502,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.78/1.51      | v1_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X1) != iProver_top
% 7.78/1.51      | v1_relat_1(X2) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1508,c_1511]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_12890,plain,
% 7.78/1.51      ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
% 7.78/1.51      | v1_relat_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X1) != iProver_top
% 7.78/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1482,c_5502]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_13535,plain,
% 7.78/1.51      ( v1_relat_1(X1) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top
% 7.78/1.51      | k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1)) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_12890,c_2738]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_13536,plain,
% 7.78/1.51      ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
% 7.78/1.51      | v1_relat_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.51      inference(renaming,[status(thm)],[c_13535]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_13543,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK3),sK3),X0)
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_2738,c_13536]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_41,negated_conjecture,
% 7.78/1.51      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 7.78/1.51      inference(cnf_transformation,[],[f111]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_34,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | ~ v2_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | k2_relset_1(X1,X2,X0) != X2
% 7.78/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.78/1.51      | k1_xboole_0 = X2 ),
% 7.78/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1490,plain,
% 7.78/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.78/1.51      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.78/1.51      | k1_xboole_0 = X1
% 7.78/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v2_funct_1(X2) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_0,plain,
% 7.78/1.51      ( v1_xboole_0(o_0_0_xboole_0) ),
% 7.78/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1516,plain,
% 7.78/1.51      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1,plain,
% 7.78/1.51      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.78/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1515,plain,
% 7.78/1.51      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_2667,plain,
% 7.78/1.51      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1516,c_1515]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4228,plain,
% 7.78/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.78/1.51      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.78/1.51      | o_0_0_xboole_0 = X1
% 7.78/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v2_funct_1(X2) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.78/1.51      inference(demodulation,[status(thm)],[c_1490,c_2667]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4232,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 7.78/1.51      | sK2 = o_0_0_xboole_0
% 7.78/1.51      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.78/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.78/1.51      | v2_funct_1(sK3) != iProver_top
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_41,c_4228]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_46,negated_conjecture,
% 7.78/1.51      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.78/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_39,negated_conjecture,
% 7.78/1.51      ( v2_funct_1(sK3) ),
% 7.78/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_37,negated_conjecture,
% 7.78/1.51      ( k1_xboole_0 != sK2 ),
% 7.78/1.51      inference(cnf_transformation,[],[f115]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1581,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,sK2)
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 7.78/1.51      | ~ v2_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | k2_relset_1(X1,sK2,X0) != sK2
% 7.78/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK2)
% 7.78/1.51      | k1_xboole_0 = sK2 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_34]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1676,plain,
% 7.78/1.51      ( ~ v1_funct_2(sK3,X0,sK2)
% 7.78/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 7.78/1.51      | ~ v2_funct_1(sK3)
% 7.78/1.51      | ~ v1_funct_1(sK3)
% 7.78/1.51      | k2_relset_1(X0,sK2,sK3) != sK2
% 7.78/1.51      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 7.78/1.51      | k1_xboole_0 = sK2 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_1581]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1814,plain,
% 7.78/1.51      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.78/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.78/1.51      | ~ v2_funct_1(sK3)
% 7.78/1.51      | ~ v1_funct_1(sK3)
% 7.78/1.51      | k2_relset_1(sK1,sK2,sK3) != sK2
% 7.78/1.51      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 7.78/1.51      | k1_xboole_0 = sK2 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_1676]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4473,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_4232,c_47,c_46,c_45,c_41,c_39,c_37,c_1814]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_13549,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK2),X0)
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(light_normalisation,[status(thm)],[c_13543,c_4473]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_13576,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,sK4)) = k5_relat_1(k6_partfun1(sK2),sK4) ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_2737,c_13549]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_5,plain,
% 7.78/1.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.78/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1512,plain,
% 7.78/1.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4,plain,
% 7.78/1.51      ( k2_subset_1(X0) = X0 ),
% 7.78/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1517,plain,
% 7.78/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.78/1.51      inference(light_normalisation,[status(thm)],[c_1512,c_4]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1488,plain,
% 7.78/1.51      ( v2_funct_1(sK3) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_15,plain,
% 7.78/1.51      ( ~ v2_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_relat_1(X0)
% 7.78/1.51      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.78/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1506,plain,
% 7.78/1.51      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.78/1.51      | v2_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4376,plain,
% 7.78/1.51      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top
% 7.78/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1488,c_1506]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_48,plain,
% 7.78/1.51      ( v1_funct_1(sK3) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4476,plain,
% 7.78/1.51      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_4376,c_48,c_2738]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_6,plain,
% 7.78/1.51      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.78/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_11,plain,
% 7.78/1.51      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.78/1.51      | ~ v1_relat_1(X0)
% 7.78/1.51      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.78/1.51      inference(cnf_transformation,[],[f120]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_461,plain,
% 7.78/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.51      | ~ v1_relat_1(X2)
% 7.78/1.51      | X3 != X1
% 7.78/1.51      | k5_relat_1(X2,k6_partfun1(X3)) = X2
% 7.78/1.51      | k2_relat_1(X2) != X0 ),
% 7.78/1.51      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_462,plain,
% 7.78/1.51      ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 7.78/1.51      | ~ v1_relat_1(X0)
% 7.78/1.51      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.78/1.51      inference(unflattening,[status(thm)],[c_461]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1481,plain,
% 7.78/1.51      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 7.78/1.51      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1)) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4478,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
% 7.78/1.51      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top
% 7.78/1.51      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_4476,c_1481]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4309,plain,
% 7.78/1.51      ( ~ v1_funct_1(sK3)
% 7.78/1.51      | v1_relat_1(k2_funct_1(sK3))
% 7.78/1.51      | ~ v1_relat_1(sK3) ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4310,plain,
% 7.78/1.51      ( v1_funct_1(sK3) != iProver_top
% 7.78/1.51      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 7.78/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_4309]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4697,plain,
% 7.78/1.51      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top
% 7.78/1.51      | k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_4478,c_48,c_2738,c_4310]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4698,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
% 7.78/1.51      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) != iProver_top ),
% 7.78/1.51      inference(renaming,[status(thm)],[c_4697]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_20,plain,
% 7.78/1.51      ( ~ v2_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_relat_1(X0)
% 7.78/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.78/1.51      inference(cnf_transformation,[],[f123]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1501,plain,
% 7.78/1.51      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.78/1.51      | v2_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4442,plain,
% 7.78/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top
% 7.78/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1488,c_1501]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_35,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | ~ v2_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | k2_relset_1(X1,X2,X0) != X2
% 7.78/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.78/1.51      | k1_xboole_0 = X2 ),
% 7.78/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1489,plain,
% 7.78/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.78/1.51      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.78/1.51      | k1_xboole_0 = X1
% 7.78/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v2_funct_1(X2) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_3753,plain,
% 7.78/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.78/1.51      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.78/1.51      | o_0_0_xboole_0 = X1
% 7.78/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v2_funct_1(X2) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.78/1.51      inference(demodulation,[status(thm)],[c_1489,c_2667]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_3757,plain,
% 7.78/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.78/1.51      | sK2 = o_0_0_xboole_0
% 7.78/1.51      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.78/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.78/1.51      | v2_funct_1(sK3) != iProver_top
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_41,c_3753]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1582,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,sK2)
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 7.78/1.51      | ~ v2_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | k2_relset_1(X1,sK2,X0) != sK2
% 7.78/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.78/1.51      | k1_xboole_0 = sK2 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_35]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1702,plain,
% 7.78/1.51      ( ~ v1_funct_2(sK3,X0,sK2)
% 7.78/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 7.78/1.51      | ~ v2_funct_1(sK3)
% 7.78/1.51      | ~ v1_funct_1(sK3)
% 7.78/1.51      | k2_relset_1(X0,sK2,sK3) != sK2
% 7.78/1.51      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
% 7.78/1.51      | k1_xboole_0 = sK2 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_1582]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1827,plain,
% 7.78/1.51      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.78/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.78/1.51      | ~ v2_funct_1(sK3)
% 7.78/1.51      | ~ v1_funct_1(sK3)
% 7.78/1.51      | k2_relset_1(sK1,sK2,sK3) != sK2
% 7.78/1.51      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.78/1.51      | k1_xboole_0 = sK2 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_1702]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_3911,plain,
% 7.78/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_3757,c_47,c_46,c_45,c_41,c_39,c_37,c_1827]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4443,plain,
% 7.78/1.51      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top
% 7.78/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.78/1.51      inference(light_normalisation,[status(thm)],[c_4442,c_3911]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4644,plain,
% 7.78/1.51      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_4443,c_48,c_2738]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_8,plain,
% 7.78/1.51      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.78/1.51      inference(cnf_transformation,[],[f117]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4656,plain,
% 7.78/1.51      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_4644,c_8]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4657,plain,
% 7.78/1.51      ( k1_relat_1(sK3) = sK1 ),
% 7.78/1.51      inference(demodulation,[status(thm)],[c_4656,c_8]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4703,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(X0)) = k2_funct_1(sK3)
% 7.78/1.51      | m1_subset_1(sK1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.78/1.51      inference(light_normalisation,[status(thm)],[c_4698,c_4657]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4707,plain,
% 7.78/1.51      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(sK1)) = k2_funct_1(sK3) ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1517,c_4703]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_24,plain,
% 7.78/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.78/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.78/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.78/1.51      | X3 = X2 ),
% 7.78/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_40,negated_conjecture,
% 7.78/1.51      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 7.78/1.51      inference(cnf_transformation,[],[f112]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_517,plain,
% 7.78/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | X3 = X0
% 7.78/1.51      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 7.78/1.51      | k6_partfun1(sK1) != X3
% 7.78/1.51      | sK1 != X2
% 7.78/1.51      | sK1 != X1 ),
% 7.78/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_40]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_518,plain,
% 7.78/1.51      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.78/1.51      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.78/1.51      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 7.78/1.51      inference(unflattening,[status(thm)],[c_517]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_27,plain,
% 7.78/1.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.78/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_526,plain,
% 7.78/1.51      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.78/1.51      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 7.78/1.51      inference(forward_subsumption_resolution,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_518,c_27]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1479,plain,
% 7.78/1.51      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.78/1.51      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_44,negated_conjecture,
% 7.78/1.51      ( v1_funct_1(sK4) ),
% 7.78/1.51      inference(cnf_transformation,[],[f108]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_25,plain,
% 7.78/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.78/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X3) ),
% 7.78/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1760,plain,
% 7.78/1.51      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.78/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.78/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.78/1.51      | ~ v1_funct_1(sK4)
% 7.78/1.51      | ~ v1_funct_1(sK3) ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_25]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_2474,plain,
% 7.78/1.51      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_1479,c_47,c_45,c_44,c_42,c_526,c_1760]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_31,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.78/1.51      | ~ v1_funct_2(X3,X4,X1)
% 7.78/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | v2_funct_1(X0)
% 7.78/1.51      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X3)
% 7.78/1.51      | k2_relset_1(X4,X1,X3) != X1
% 7.78/1.51      | k1_xboole_0 = X2 ),
% 7.78/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1493,plain,
% 7.78/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.78/1.51      | k1_xboole_0 = X3
% 7.78/1.51      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.78/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.78/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v2_funct_1(X4) = iProver_top
% 7.78/1.51      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.78/1.51      | v1_funct_1(X4) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7434,plain,
% 7.78/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.78/1.51      | o_0_0_xboole_0 = X3
% 7.78/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.78/1.51      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.78/1.51      | v2_funct_1(X4) = iProver_top
% 7.78/1.51      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top
% 7.78/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.78/1.51      inference(demodulation,[status(thm)],[c_1493,c_2667]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7436,plain,
% 7.78/1.51      ( o_0_0_xboole_0 = X0
% 7.78/1.51      | v1_funct_2(X1,sK2,X0) != iProver_top
% 7.78/1.51      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.78/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.78/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.78/1.51      | v2_funct_1(X1) = iProver_top
% 7.78/1.51      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 7.78/1.51      | v1_funct_1(X1) != iProver_top
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_41,c_7434]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_49,plain,
% 7.78/1.51      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_50,plain,
% 7.78/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7611,plain,
% 7.78/1.51      ( v1_funct_1(X1) != iProver_top
% 7.78/1.51      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 7.78/1.51      | v2_funct_1(X1) = iProver_top
% 7.78/1.51      | v1_funct_2(X1,sK2,X0) != iProver_top
% 7.78/1.51      | o_0_0_xboole_0 = X0
% 7.78/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_7436,c_48,c_49,c_50]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7612,plain,
% 7.78/1.51      ( o_0_0_xboole_0 = X0
% 7.78/1.51      | v1_funct_2(X1,sK2,X0) != iProver_top
% 7.78/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.78/1.51      | v2_funct_1(X1) = iProver_top
% 7.78/1.51      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 7.78/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.51      inference(renaming,[status(thm)],[c_7611]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7617,plain,
% 7.78/1.51      ( sK1 = o_0_0_xboole_0
% 7.78/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.78/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.78/1.51      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 7.78/1.51      | v2_funct_1(sK4) = iProver_top
% 7.78/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_2474,c_7612]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_51,plain,
% 7.78/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_43,negated_conjecture,
% 7.78/1.51      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.78/1.51      inference(cnf_transformation,[],[f109]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_52,plain,
% 7.78/1.51      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_53,plain,
% 7.78/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_38,negated_conjecture,
% 7.78/1.51      ( k1_xboole_0 != sK1 ),
% 7.78/1.51      inference(cnf_transformation,[],[f114]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1599,plain,
% 7.78/1.51      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_848,plain,
% 7.78/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.78/1.51      theory(equality) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1649,plain,
% 7.78/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_848]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1936,plain,
% 7.78/1.51      ( v1_xboole_0(sK1)
% 7.78/1.51      | ~ v1_xboole_0(o_0_0_xboole_0)
% 7.78/1.51      | sK1 != o_0_0_xboole_0 ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_1649]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_14,plain,
% 7.78/1.51      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.78/1.51      inference(cnf_transformation,[],[f121]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_3540,plain,
% 7.78/1.51      ( v2_funct_1(k6_partfun1(sK1)) ),
% 7.78/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_3541,plain,
% 7.78/1.51      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_3540]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7834,plain,
% 7.78/1.51      ( v2_funct_1(sK4) = iProver_top ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_7617,c_51,c_52,c_53,c_38,c_0,c_1599,c_1936,c_3541]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_18,plain,
% 7.78/1.51      ( ~ v2_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_relat_1(X0)
% 7.78/1.51      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.78/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1503,plain,
% 7.78/1.51      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 7.78/1.51      | v2_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_funct_1(X0) != iProver_top
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7839,plain,
% 7.78/1.51      ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 7.78/1.51      | v1_funct_1(sK4) != iProver_top
% 7.78/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_7834,c_1503]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_29,plain,
% 7.78/1.51      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.78/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.78/1.51      | ~ v1_funct_2(X3,X1,X0)
% 7.78/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.78/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.78/1.51      | ~ v1_funct_1(X2)
% 7.78/1.51      | ~ v1_funct_1(X3)
% 7.78/1.51      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.78/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_530,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.78/1.51      | ~ v1_funct_2(X3,X2,X1)
% 7.78/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X3)
% 7.78/1.51      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.78/1.51      | k2_relset_1(X1,X2,X0) = X2
% 7.78/1.51      | k6_partfun1(X2) != k6_partfun1(sK1)
% 7.78/1.51      | sK1 != X2 ),
% 7.78/1.51      inference(resolution_lifted,[status(thm)],[c_29,c_40]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_531,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,sK1)
% 7.78/1.51      | ~ v1_funct_2(X2,sK1,X1)
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.78/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X2)
% 7.78/1.51      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.78/1.51      | k2_relset_1(X1,sK1,X0) = sK1
% 7.78/1.51      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 7.78/1.51      inference(unflattening,[status(thm)],[c_530]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_624,plain,
% 7.78/1.51      ( ~ v1_funct_2(X0,X1,sK1)
% 7.78/1.51      | ~ v1_funct_2(X2,sK1,X1)
% 7.78/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.78/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X2)
% 7.78/1.51      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.78/1.51      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 7.78/1.51      inference(equality_resolution_simp,[status(thm)],[c_531]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1478,plain,
% 7.78/1.51      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 7.78/1.51      | k2_relset_1(X0,sK1,X2) = sK1
% 7.78/1.51      | v1_funct_2(X2,X0,sK1) != iProver_top
% 7.78/1.51      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.78/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top
% 7.78/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1975,plain,
% 7.78/1.51      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 7.78/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.78/1.51      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.78/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.78/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.78/1.51      | v1_funct_1(sK4) != iProver_top
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.51      inference(equality_resolution,[status(thm)],[c_1478]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_2481,plain,
% 7.78/1.51      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_1975,c_48,c_49,c_50,c_51,c_52,c_53]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_3758,plain,
% 7.78/1.51      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 7.78/1.51      | sK1 = o_0_0_xboole_0
% 7.78/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.78/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.78/1.51      | v2_funct_1(sK4) != iProver_top
% 7.78/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_2481,c_3753]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4036,plain,
% 7.78/1.51      ( v2_funct_1(sK4) != iProver_top
% 7.78/1.51      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_3758,c_51,c_52,c_53,c_38,c_0,c_1599,c_1936]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_4037,plain,
% 7.78/1.51      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 7.78/1.51      | v2_funct_1(sK4) != iProver_top ),
% 7.78/1.51      inference(renaming,[status(thm)],[c_4036]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7845,plain,
% 7.78/1.51      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_7834,c_4037]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7850,plain,
% 7.78/1.51      ( k1_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4)
% 7.78/1.51      | v1_funct_1(sK4) != iProver_top
% 7.78/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.78/1.51      inference(demodulation,[status(thm)],[c_7839,c_7845]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_9,plain,
% 7.78/1.51      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.78/1.51      inference(cnf_transformation,[],[f118]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7851,plain,
% 7.78/1.51      ( k1_relat_1(sK4) = sK2
% 7.78/1.51      | v1_funct_1(sK4) != iProver_top
% 7.78/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.78/1.51      inference(demodulation,[status(thm)],[c_7850,c_9]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_8789,plain,
% 7.78/1.51      ( k1_relat_1(sK4) = sK2 ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_7851,c_51,c_2737]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_10,plain,
% 7.78/1.51      ( ~ v1_relat_1(X0)
% 7.78/1.51      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.78/1.51      inference(cnf_transformation,[],[f119]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1510,plain,
% 7.78/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_3417,plain,
% 7.78/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(sK4)),sK4) = sK4 ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_2737,c_1510]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_8791,plain,
% 7.78/1.51      ( k5_relat_1(k6_partfun1(sK2),sK4) = sK4 ),
% 7.78/1.51      inference(demodulation,[status(thm)],[c_8789,c_3417]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_28,plain,
% 7.78/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.78/1.51      | ~ v1_funct_1(X0)
% 7.78/1.51      | ~ v1_funct_1(X3)
% 7.78/1.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.78/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_1495,plain,
% 7.78/1.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.78/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.78/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v1_funct_1(X5) != iProver_top
% 7.78/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.78/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7535,plain,
% 7.78/1.51      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top
% 7.78/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1487,c_1495]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7620,plain,
% 7.78/1.51      ( v1_funct_1(X2) != iProver_top
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_7535,c_51]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7621,plain,
% 7.78/1.51      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.78/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.78/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.78/1.51      inference(renaming,[status(thm)],[c_7620]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7629,plain,
% 7.78/1.51      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.51      inference(superposition,[status(thm)],[c_1484,c_7621]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_7631,plain,
% 7.78/1.51      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 7.78/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.78/1.51      inference(light_normalisation,[status(thm)],[c_7629,c_2474]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_8936,plain,
% 7.78/1.51      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 7.78/1.51      inference(global_propositional_subsumption,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_7631,c_48]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_13585,plain,
% 7.78/1.51      ( k2_funct_1(sK3) = sK4 ),
% 7.78/1.51      inference(light_normalisation,
% 7.78/1.51                [status(thm)],
% 7.78/1.51                [c_13576,c_4707,c_8791,c_8936]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(c_36,negated_conjecture,
% 7.78/1.51      ( k2_funct_1(sK3) != sK4 ),
% 7.78/1.51      inference(cnf_transformation,[],[f116]) ).
% 7.78/1.51  
% 7.78/1.51  cnf(contradiction,plain,
% 7.78/1.51      ( $false ),
% 7.78/1.51      inference(minisat,[status(thm)],[c_13585,c_36]) ).
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.51  
% 7.78/1.51  ------                               Statistics
% 7.78/1.51  
% 7.78/1.51  ------ General
% 7.78/1.51  
% 7.78/1.51  abstr_ref_over_cycles:                  0
% 7.78/1.51  abstr_ref_under_cycles:                 0
% 7.78/1.51  gc_basic_clause_elim:                   0
% 7.78/1.51  forced_gc_time:                         0
% 7.78/1.51  parsing_time:                           0.014
% 7.78/1.51  unif_index_cands_time:                  0.
% 7.78/1.51  unif_index_add_time:                    0.
% 7.78/1.51  orderings_time:                         0.
% 7.78/1.51  out_proof_time:                         0.026
% 7.78/1.51  total_time:                             0.635
% 7.78/1.51  num_of_symbols:                         56
% 7.78/1.51  num_of_terms:                           22659
% 7.78/1.51  
% 7.78/1.51  ------ Preprocessing
% 7.78/1.51  
% 7.78/1.51  num_of_splits:                          0
% 7.78/1.51  num_of_split_atoms:                     0
% 7.78/1.51  num_of_reused_defs:                     0
% 7.78/1.51  num_eq_ax_congr_red:                    4
% 7.78/1.51  num_of_sem_filtered_clauses:            1
% 7.78/1.51  num_of_subtypes:                        0
% 7.78/1.51  monotx_restored_types:                  0
% 7.78/1.51  sat_num_of_epr_types:                   0
% 7.78/1.51  sat_num_of_non_cyclic_types:            0
% 7.78/1.51  sat_guarded_non_collapsed_types:        0
% 7.78/1.51  num_pure_diseq_elim:                    0
% 7.78/1.51  simp_replaced_by:                       0
% 7.78/1.51  res_preprocessed:                       221
% 7.78/1.51  prep_upred:                             0
% 7.78/1.51  prep_unflattend:                        14
% 7.78/1.51  smt_new_axioms:                         0
% 7.78/1.51  pred_elim_cands:                        6
% 7.78/1.51  pred_elim:                              2
% 7.78/1.51  pred_elim_cl:                           2
% 7.78/1.51  pred_elim_cycles:                       4
% 7.78/1.51  merged_defs:                            0
% 7.78/1.51  merged_defs_ncl:                        0
% 7.78/1.51  bin_hyper_res:                          0
% 7.78/1.51  prep_cycles:                            4
% 7.78/1.51  pred_elim_time:                         0.008
% 7.78/1.51  splitting_time:                         0.
% 7.78/1.51  sem_filter_time:                        0.
% 7.78/1.51  monotx_time:                            0.001
% 7.78/1.51  subtype_inf_time:                       0.
% 7.78/1.51  
% 7.78/1.51  ------ Problem properties
% 7.78/1.51  
% 7.78/1.51  clauses:                                46
% 7.78/1.51  conjectures:                            11
% 7.78/1.51  epr:                                    11
% 7.78/1.51  horn:                                   42
% 7.78/1.51  ground:                                 14
% 7.78/1.51  unary:                                  19
% 7.78/1.51  binary:                                 5
% 7.78/1.51  lits:                                   152
% 7.78/1.51  lits_eq:                                37
% 7.78/1.51  fd_pure:                                0
% 7.78/1.51  fd_pseudo:                              0
% 7.78/1.51  fd_cond:                                5
% 7.78/1.51  fd_pseudo_cond:                         1
% 7.78/1.51  ac_symbols:                             0
% 7.78/1.51  
% 7.78/1.51  ------ Propositional Solver
% 7.78/1.51  
% 7.78/1.51  prop_solver_calls:                      30
% 7.78/1.51  prop_fast_solver_calls:                 2206
% 7.78/1.51  smt_solver_calls:                       0
% 7.78/1.51  smt_fast_solver_calls:                  0
% 7.78/1.51  prop_num_of_clauses:                    7380
% 7.78/1.51  prop_preprocess_simplified:             15064
% 7.78/1.51  prop_fo_subsumed:                       136
% 7.78/1.51  prop_solver_time:                       0.
% 7.78/1.51  smt_solver_time:                        0.
% 7.78/1.51  smt_fast_solver_time:                   0.
% 7.78/1.51  prop_fast_solver_time:                  0.
% 7.78/1.51  prop_unsat_core_time:                   0.001
% 7.78/1.51  
% 7.78/1.51  ------ QBF
% 7.78/1.51  
% 7.78/1.51  qbf_q_res:                              0
% 7.78/1.51  qbf_num_tautologies:                    0
% 7.78/1.51  qbf_prep_cycles:                        0
% 7.78/1.51  
% 7.78/1.51  ------ BMC1
% 7.78/1.51  
% 7.78/1.51  bmc1_current_bound:                     -1
% 7.78/1.51  bmc1_last_solved_bound:                 -1
% 7.78/1.51  bmc1_unsat_core_size:                   -1
% 7.78/1.51  bmc1_unsat_core_parents_size:           -1
% 7.78/1.51  bmc1_merge_next_fun:                    0
% 7.78/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.78/1.51  
% 7.78/1.51  ------ Instantiation
% 7.78/1.51  
% 7.78/1.51  inst_num_of_clauses:                    1796
% 7.78/1.51  inst_num_in_passive:                    129
% 7.78/1.51  inst_num_in_active:                     983
% 7.78/1.51  inst_num_in_unprocessed:                684
% 7.78/1.51  inst_num_of_loops:                      1110
% 7.78/1.51  inst_num_of_learning_restarts:          0
% 7.78/1.51  inst_num_moves_active_passive:          125
% 7.78/1.51  inst_lit_activity:                      0
% 7.78/1.51  inst_lit_activity_moves:                1
% 7.78/1.51  inst_num_tautologies:                   0
% 7.78/1.51  inst_num_prop_implied:                  0
% 7.78/1.51  inst_num_existing_simplified:           0
% 7.78/1.51  inst_num_eq_res_simplified:             0
% 7.78/1.51  inst_num_child_elim:                    0
% 7.78/1.51  inst_num_of_dismatching_blockings:      301
% 7.78/1.51  inst_num_of_non_proper_insts:           1462
% 7.78/1.51  inst_num_of_duplicates:                 0
% 7.78/1.51  inst_inst_num_from_inst_to_res:         0
% 7.78/1.51  inst_dismatching_checking_time:         0.
% 7.78/1.51  
% 7.78/1.51  ------ Resolution
% 7.78/1.51  
% 7.78/1.51  res_num_of_clauses:                     0
% 7.78/1.51  res_num_in_passive:                     0
% 7.78/1.51  res_num_in_active:                      0
% 7.78/1.51  res_num_of_loops:                       225
% 7.78/1.51  res_forward_subset_subsumed:            113
% 7.78/1.51  res_backward_subset_subsumed:           0
% 7.78/1.51  res_forward_subsumed:                   0
% 7.78/1.51  res_backward_subsumed:                  0
% 7.78/1.51  res_forward_subsumption_resolution:     2
% 7.78/1.51  res_backward_subsumption_resolution:    0
% 7.78/1.51  res_clause_to_clause_subsumption:       897
% 7.78/1.51  res_orphan_elimination:                 0
% 7.78/1.51  res_tautology_del:                      37
% 7.78/1.51  res_num_eq_res_simplified:              1
% 7.78/1.51  res_num_sel_changes:                    0
% 7.78/1.51  res_moves_from_active_to_pass:          0
% 7.78/1.51  
% 7.78/1.51  ------ Superposition
% 7.78/1.51  
% 7.78/1.51  sup_time_total:                         0.
% 7.78/1.51  sup_time_generating:                    0.
% 7.78/1.51  sup_time_sim_full:                      0.
% 7.78/1.51  sup_time_sim_immed:                     0.
% 7.78/1.51  
% 7.78/1.51  sup_num_of_clauses:                     413
% 7.78/1.51  sup_num_in_active:                      207
% 7.78/1.51  sup_num_in_passive:                     206
% 7.78/1.51  sup_num_of_loops:                       221
% 7.78/1.51  sup_fw_superposition:                   297
% 7.78/1.51  sup_bw_superposition:                   131
% 7.78/1.51  sup_immediate_simplified:               108
% 7.78/1.51  sup_given_eliminated:                   3
% 7.78/1.51  comparisons_done:                       0
% 7.78/1.51  comparisons_avoided:                    0
% 7.78/1.51  
% 7.78/1.51  ------ Simplifications
% 7.78/1.51  
% 7.78/1.51  
% 7.78/1.51  sim_fw_subset_subsumed:                 5
% 7.78/1.51  sim_bw_subset_subsumed:                 12
% 7.78/1.51  sim_fw_subsumed:                        16
% 7.78/1.51  sim_bw_subsumed:                        1
% 7.78/1.51  sim_fw_subsumption_res:                 0
% 7.78/1.51  sim_bw_subsumption_res:                 0
% 7.78/1.51  sim_tautology_del:                      2
% 7.78/1.51  sim_eq_tautology_del:                   13
% 7.78/1.51  sim_eq_res_simp:                        0
% 7.78/1.51  sim_fw_demodulated:                     13
% 7.78/1.51  sim_bw_demodulated:                     18
% 7.78/1.51  sim_light_normalised:                   98
% 7.78/1.51  sim_joinable_taut:                      0
% 7.78/1.51  sim_joinable_simp:                      0
% 7.78/1.51  sim_ac_normalised:                      0
% 7.78/1.51  sim_smt_subsumption:                    0
% 7.78/1.51  
%------------------------------------------------------------------------------
